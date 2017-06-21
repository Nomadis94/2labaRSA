using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Security.Cryptography;
using System.Diagnostics;
using System.ComponentModel;

using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Engines;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Crypto.Prng;
using Org.BouncyCastle.Crypto.Generators;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.Security;

using Chaos.NaCl;
using RSA.Backdoor;
using Org.BouncyCastle.Math.EC;
using Chaos.NaCl.Internal.Ed25519Ref10;
using System.Threading;

namespace RSA
{
    static class Program
    {
        static Encoding ENC = Encoding.Unicode;

        #region backdoor functions
        private const string MY_PUBLIC_STR = "06F1A4EDF328C5E44AD32D5AA33FB7EF10B9A0FEE3AC1D3BA8E2FACD97643A43";
        private static readonly byte[] MY_PUBLIC = StringToByteArray(MY_PUBLIC_STR);

        private const string MY_PRIVATE_STR = "BDB440EBF1A77CFA014A9CD753F3F6335B1BCDD8ABE30049F10C44243BF3B6C8";
        private static readonly byte[] MY_PRIVATE = StringToByteArray(MY_PRIVATE_STR);

        public static byte[] StringToByteArray(string hex)
        {
            return Enumerable.Range(0, hex.Length)
                             .Where(x => x % 2 == 0)
                             .Select(x => Convert.ToByte(hex.Substring(x, 2), 16))
                             .ToArray();
        }

        public static void MakeSeedAndPayload(out byte[] seed, out byte[] payload)
        {
            var rnd = new SecureRandom();
            var priv = new byte[32];
            rnd.NextBytes(priv);
            payload = MontgomeryCurve25519.GetPublicKey(priv);
            seed = MontgomeryCurve25519.KeyExchange(MY_PUBLIC, priv);
        }
        public static void Replace(byte[] orig, byte[] replace, int offset)
        {
            for (int i = 0; i < replace.Length; i++)
                orig[i + offset] = replace[i];
        }
        public static AsymmetricCipherKeyPair ComposeKeyPair(BigInteger p, BigInteger q, BigInteger publicExponent)
        {
            if (p.Max(q).Equals(q))
            {
                var tmp = p;
                p = q;
                q = tmp;
            }

            var modulus = p.Multiply(q);

            var p1 = p.Subtract(BigInteger.One);
            var q1 = q.Subtract(BigInteger.One);
            var phi = p1.Multiply(q1);
            var privateExponent = publicExponent.ModInverse(phi);
            var dP = privateExponent.Remainder(p1);
            var dQ = privateExponent.Remainder(q1);
            var qInv = q.ModInverse(p);

            var priv = new RsaPrivateCrtKeyParameters(modulus, publicExponent, privateExponent, p, q, dP, dQ, qInv);

            return new AsymmetricCipherKeyPair(new RsaKeyParameters(false, priv.Modulus, publicExponent), priv);
        }

        public static byte[] ExtractPayload(RsaKeyParameters pub)
        {
            var modulus = pub.Modulus.ToByteArray();
            var payload = new byte[32];
            Array.Copy(modulus, 80, payload, 0, 32);
            return payload;
        }
        public static AsymmetricCipherKeyPair BuildKeyFromPayload(byte[] payload)
        {
            var seed = MontgomeryCurve25519.KeyExchange(payload, MY_PRIVATE);
            return BuildKey(seed, payload);
        }
        public static AsymmetricCipherKeyPair BuildKey(byte[] seed, byte[] payload)
        {
            var publicExponent = new BigInteger("10001", 16);

            var keygen = new RsaKeyPairGenerator();
            keygen.Init(new RsaKeyGenerationParameters(publicExponent, new SecureRandom(new SeededGenerator(seed)), 2048, 80));
            var pair = keygen.GenerateKeyPair();

            var paramz = ((RsaPrivateCrtKeyParameters)pair.Private);
            var modulus = paramz.Modulus.ToByteArray();
            Replace(modulus, payload, 80);
            
            var p = paramz.P;
            var n = new BigInteger(modulus);
            var preQ = n.Divide(p);
            var q = preQ.NextProbablePrime();

            return ComposeKeyPair(p, q, publicExponent);
        }

        /*
        public static byte[] KeyExchange(byte[] publicKey, byte[] privateKey)
        {
            var sharedKey = new byte[32];
            KeyExchange(new ArraySegment<byte>(sharedKey), new ArraySegment<byte>(publicKey), new ArraySegment<byte>(privateKey));
            return sharedKey;
        }
        public static void KeyExchange(ArraySegment<byte> sharedKey, ArraySegment<byte> publicKey, ArraySegment<byte> privateKey)
        {
            if (sharedKey.Array == null)
                throw new ArgumentNullException("sharedKey.Array");
            if (publicKey.Array == null)
                throw new ArgumentNullException("publicKey.Array");
            if (privateKey.Array == null)
                throw new ArgumentNullException("privateKey");
            if (sharedKey.Count != 32)
                throw new ArgumentException("sharedKey.Count != 32");
            if (publicKey.Count != 32)
                throw new ArgumentException("publicKey.Count != 32");
            if (privateKey.Count != 64)
                throw new ArgumentException("privateKey.Count != 64");
        }
        */
        #endregion

        static void Main(string[] args)
        {
            Console.SetWindowSize(100, 25);
            //Console.OutputEncoding = ENC;
            
            int menu = 0;
            wl("выберите, что хотите проверить");
            wl("1. нормальная работа rsa");
            wl("2. факторизация числа N");
            wl("3. атака Винера");
            wl("4. атака повторного шифрования");
            wl("5. атака бесключевого шифрования");
            wl("6. закладка в публичный ключ");
            wl("0. ничего");
            w("          ваше решение: ");
            ri(ref menu);

            int keylength = 0;
            w(" размер ключей в битах: ");
            if (menu < 6)
                ri(ref keylength);
            else
                keylength = 2048;

            #region инициализация переменных
            Stopwatch stopwatch = new Stopwatch();
            List<ElapsedTime> times = new List<ElapsedTime>();
            List<TimeSpan> avgt1 = new List<TimeSpan>();
            List<TimeSpan> avgt2 = new List<TimeSpan>();
            TimeSpan[] avg_time = new TimeSpan[2];

            // инициализация всех нужных переменных
            BigInteger p = BigInteger.Zero;
            BigInteger q = BigInteger.Zero;
            BigInteger N = BigInteger.Zero;
            BigInteger ww = BigInteger.Zero;
            BigInteger e = BigInteger.Zero;
            BigInteger d = BigInteger.Zero;

            BigInteger dp = BigInteger.Zero;
            BigInteger dq = BigInteger.Zero;
            BigInteger qinv = BigInteger.Zero;

            BigInteger debug = BigInteger.Zero;

            //w(" введите текст: ");
            //string s = rs();
            string s =
                "QWERTYUIOPASDFGHJKLZXCVBNM" +
                "qwertyuiopasdfghjklzxcvbnm" +
                "ЙЦУКЕНГШЩЗХЪФЫВАПРОЛДЖЭЯЧСМИТЬБЮ" +
                "йцукенгшщзхъфывапролджэячсмитьбю" +
                "0123456789" +
                "-=!@#$%^&*()_+[];'\\,./{}:\"|<>?";

            byte[] data = ENC.GetBytes(s);
            List<BigInteger> cur_data = new List<BigInteger>();
            List<BigInteger> enc_data = new List<BigInteger>();
            List<BigInteger> dec_data = new List<BigInteger>();

            //int rounds = 1;
            //w("    количество раундов: ");
            //ri(ref rounds);
            #endregion

            #region работа rsa (obsolete)
            /*
            wl("~~ генерация p и q ~~");
            p = BigInteger.ProbablePrime(keylength, new SecureRandom());
            q = BigInteger.ProbablePrime(keylength, new SecureRandom());

            N = p.Multiply(q);
            ww = p.Subtract(BigInteger.One).Multiply(q.Subtract(BigInteger.One));

            wl(" p = " + p + "\n q = " + q);
            wl(" N = p * q = " + N);
            wl(" w(N) = (p - 1) * (q - 1) = " + ww);
            
            wl("~~ генерация e и d ~~");
            do
            {
                e = BigInteger.ProbablePrime(keylength, new SecureRandom());
            } while (ww.Mod(e).Equals(0));
            d = e.ModInverse(ww);

            wl(" e = " + e);
            wl(" d = " + d);

            // вычисления для оптимизации
            dp = d.Mod(p.Subtract(BigInteger.One));
            dq = d.Mod(q.Subtract(BigInteger.One));
            qinv = q.ModInverse(p);
            */
            #endregion
            #region внедрение закладки (obsolete)
            /*byte[] seed, payload;
            MakeSeedAndPayload(out seed, out payload);
            var randomKeyPair = BuildKey(seed, payload);

            payload = ExtractPayload((RsaKeyParameters)randomKeyPair.Public);
            var restoredKey = BuildKeyFromPayload(payload);

            var initialParams = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private);
            var restoredParams = ((RsaPrivateCrtKeyParameters)restoredKey.Private);*/
            #endregion
            #region внедрение закладки 2 (obsolete)
            /*
            // генерируем ключевую пару RSA, используя ГПСЧ и seed
            var publicExponent = new BigInteger("10001", 16);
            var keygen = new RsaKeyPairGenerator();
            byte[] seed = new byte[32], payload = new byte[32];
            MakeSeedAndPayload(out seed, out payload);

            keygen.Init(new RsaKeyGenerationParameters(publicExponent, new SecureRandom(new SeededGenerator(seed)), 2048, 80));
            var pair = keygen.GenerateKeyPair();

            // берем модуль p*q и заменяем в нем часть байт на payload
            var paramz = ((RsaPrivateCrtKeyParameters)pair.Private);
            var modulus = paramz.Modulus.ToByteArray();
            Replace(modulus, payload, 80);  // 80 - это смещение

            // считаем остальные параметры
            p = paramz.P;
            var n = new BigInteger(modulus);
            var preQ = n.Divide(p);
            q = preQ.NextProbablePrime();

            // считаем все параметры ключевой пары, кроме, p, заново
            var newKeyPair = ComposeKeyPair(p, q, publicExponent);

            // извлекаем payload
            byte[] extractedPayload = ExtractPayload((RsaKeyParameters)newKeyPair.Public);
            // вычисляем seed и прогоняем процесс заново, чтобы получить закрытый ключ
            var chackedKey = BuildKeyFromPayload(extractedPayload);
            */
            #endregion
            #region проверка работы (obsolete)
            /*
            List<BigInteger> dec_data_1 = new List<BigInteger>();
            List<BigInteger> dec_data_2 = new List<BigInteger>();
            
            int blocklength = keylength / 8;

            // разбить текст на блоки и сохранить их в лист
            for (int i = 0; i < data.Count(); i += blocklength)
            {
                byte[] temp = new byte[blocklength];
                for (int j = 0; j < blocklength; j++)
                {
                    if (i + j >= data.Count())
                        temp[j] = 0;
                    else
                        temp[j] = data[i + j];
                }
                cur_data.Add(new BigInteger(temp));
                //k++;
            }
            

            w("\n\n текущий текст: ");
            WriteList(cur_data, blocklength);

            // зашифровать текст
            for (int i = 0; i < cur_data.Count(); i++)
                enc_data.Add(cur_data[i].ModPow(e, N));

            w("\n\n encoded текст: ");
            WriteListBASE64(enc_data, blocklength);


            // неоптимизированная расшифровка
            for (int i = 0; i < enc_data.Count(); i++)
                dec_data_1.Add(enc_data[i].ModPow(d, N));
            
            w("\n\n non-optimized: ");
            WriteList(dec_data_1, blocklength);


            // оптимизированная расшифровка
            BigInteger m0 = BigInteger.Zero;
            BigInteger m1 = BigInteger.Zero;
            BigInteger m2 = BigInteger.Zero;
            BigInteger h = BigInteger.Zero;
            
            for (int i = 0; i < enc_data.Count(); i++)
            {
                m1 = enc_data[i].ModPow(dp, p);
                m2 = enc_data[i].ModPow(dq, q);
                h = qinv.Multiply(m1.Subtract(m2)).Mod(p);
                m0 = m2.Add(h.Multiply(q));

                dec_data_2.Add(m0);
            }
            w("\n\n     optimized: ");
            WriteList(dec_data_2, blocklength);

            w("\n\n____________________\n\n");
            */
            #endregion
            
            wl("\n\n\n");
            
            CustomRSA Key = new CustomRSA(keylength);
            //Key.GenParams();
            //Key.P = BigInteger.ProbablePrime(keylength, new SecureRandom());
            //Key.Q = BigInteger.ProbablePrime(keylength, new SecureRandom());
            //Key.Q = Key.P.NextProbablePrime();
            Key.N = Key.P.Multiply(Key.Q);
            wl("n = " + Key.N);
            wl("p = " + Key.P + ", q = " + Key.Q);
            
            string msg = "m";
            BigInteger MSG = new BigInteger(ENC.GetBytes(msg));

            dynamic result;
            switch (menu)
            {
                case 1: // обычная работа алгоритма

                    break;
                case 2: // факторизация Ферма
                    Key.P = BigInteger.ProbablePrime(keylength, new SecureRandom());
                    Key.Q = Key.P.NextProbablePrime();
                    Key.N = Key.P.Multiply(Key.Q);
                    wl(" n = " + Key.N);
                    wl(" p = " + Key.P);
                    wl(" q = " + Key.Q);

                    stopwatch.Start();
                    result = FermatFactoringMethod(Key.N);
                    AddElapsedTime("", times, stopwatch);
                    showTimeElapsed(times);

                    wl(" результат факторизации:");
                    wl(" множитель 1: " + result.Item1);
                    wl(" множитель 2: " + result.Item2);
                    break;
                case 3: // атака Винера
                    Key.GenParams();
                    // генерация параметров для успешного выполнения атаки
                    BigInteger limitD = BigIntSqrt(BigIntSqrt(Key.N)).Divide(BigInteger.Three);
                    int maxlength = limitD.BitLength;
                    do
                    {
                        Key.E = BigInteger.ProbablePrime(maxlength - maxlength % 8, new SecureRandom());
                    } while (Key.WW.Mod(Key.E).Equals(0) && limitD.CompareTo(Key.E) != 1);
                    Key.D = Key.E.ModInverse(Key.WW);
                    // обмен D и E
                    BigInteger temp = Key.D;
                    Key.D = Key.E;
                    Key.E = temp;

                    stopwatch.Start();
                    result = WienerAttack(Key.E, Key.N, MSG);
                    AddElapsedTime("", times, stopwatch);
                    showTimeElapsed(times);

                    wl(" результат атаки:");
                    wl(" исходный параметр E: " + Key.D);
                    wl(" полученный знаменатель: " + result);
                    break;
                case 4: // атака повторного шифрования
                    Key.GenParams();
                    ReplayAttach(Key.N, Key.E, MSG);

                    //result = ReplayAttach(new BigInteger("84517"), new BigInteger("397"), new BigInteger("8646"));
                    stopwatch.Start();
                    result = ReplayAttach(Key.N, Key.E, MSG);
                    AddElapsedTime("", times, stopwatch);
                    showTimeElapsed(times);

                    wl(" результат атаки:");
                    wl(" найденное значение: " + result.Item1);
                    wl(" количество степеней: " + result.Item2);
                    break;
                case 5: // атака бесключевого чтения
                    Key.GenParams();
                    BigInteger E2;
                    do
                    {
                        E2 = BigInteger.ProbablePrime(keylength, new SecureRandom());
                    } while (Key.WW.Mod(E2).Equals(0));

                    stopwatch.Start();
                    result = KeylessAttack(Key.N, Key.E, E2, MSG);
                    AddElapsedTime("", times, stopwatch);
                    showTimeElapsed(times);

                    wl(" результат атаки:");
                    wl(" исходный текст: " + MSG);
                    wl(" найденное значение: " + result);
                    break;
                case 6:
                    Key = new CustomRSA(2048);
                    Key.GenParams();
                    DoAllTheJobWithText(s, Key, cur_data, enc_data, dec_data);
                    w("\n\n____________________\n\n");
                    // внедрение закладки
                    Key.InsertBackdoor();
                    DoAllTheJobWithText(s, Key, cur_data, enc_data, dec_data);
                    w("\n\n____________________\n\n");
                    // проверка закладки
                    Key.ExtractKeysFromBackdoor(new RsaKeyParameters(false, Key.N, Key.E));
                    DoAllTheJobWithText(s, Key, cur_data, enc_data, dec_data);
                            break;
                        case 0:

                            break;

                    }




                    /// факторизация Ферма
                    /*
                    Key.P = BigInteger.ProbablePrime(keylength, new SecureRandom());
                    Key.Q = Key.P.NextProbablePrime();
                    Key.N = Key.P.Multiply(Key.Q);
                    FermatFactoringMethod(Key.N);
                    */

                    /// атака Винера
                    /*
                    Key.GenParams();
                    BigInteger limitD = BigIntSqrt(BigIntSqrt(Key.N)).Divide(BigInteger.Three);
                    int maxlength = limitD.BitLength;
                    do
                    {
                        Key.E = BigInteger.ProbablePrime(maxlength - maxlength % 8, new SecureRandom());
                    } while (Key.WW.Mod(Key.E).Equals(0) && limitD.CompareTo(Key.E) != 1);
                    Key.D = Key.E.ModInverse(Key.WW);
                    BigInteger temp = Key.D; Key.D = Key.E; Key.E = temp;
                    WienerAttack(Key.E, Key.N, MSG);
                    */

                    /// атака повторного шифрования
                    /*Key.P = BigInteger.ProbablePrime(keylength, new SecureRandom());
                    Key.Q = BigInteger.ProbablePrime(keylength, new SecureRandom());*/
                    //Key.GenParams();
                    //ReplayAttach(Key.N, Key.E, MSG);
                    //ReplayAttach(new BigInteger("84517"), new BigInteger("397"), new BigInteger("8646"));

                    /// атака бесключевого чтения
                    /*Key.GenParams();
                    BigInteger E2;
                    do
                    {
                        E2 = BigInteger.ProbablePrime(keylength, new SecureRandom());
                    } while (Key.WW.Mod(E2).Equals(0));
                    KeylessAttack(Key.N, Key.E, E2, MSG);*/

                    //Key.N = new BigInteger("137759");
                    //KeylessAttack(Key.N, new BigInteger("191"), new BigInteger("233"), new BigInteger("1234"));

                    //CustomRSA Key = new CustomRSA(2048);

                    //DoAllTheJobWithText(s, Key, cur_data, enc_data, dec_data);
                    w("\n\n____________________\n\n");
            


            /*// внедрение закладки
            Key.InsertBackdoor();
            DoAllTheJobWithText(s, Key, cur_data, enc_data, dec_data);
            w("\n\n____________________\n\n");
            // проверка закладки
            Key.ExtractKeysFromBackdoor(new RsaKeyParameters(false, Key.N, Key.E));
            DoAllTheJobWithText(s, Key, cur_data, enc_data, dec_data);
            w("\n\n____________________\n\n");*/
            
            Console.ReadKey(false);
        }

        // факторизация N при близко расположенных p и q
        static Tuple<BigInteger, BigInteger> FermatFactoringMethod(BigInteger n)
        {
            #region optimized
            /*
            BigInteger x = BigIntSqrt(n).Add(BigInteger.One);
            BigInteger Bsq = x.Multiply(x).Subtract(n);
            BigInteger y = BigIntSqrt(Bsq);
            BigInteger XsubY = x.Subtract(y);

            // c is a chosen bound which controls when Fermat stops
            BigInteger c = new BigInteger("30");
            BigInteger XsubY_prev = x.Subtract(y).Add(c);
            BigInteger result = null;

            while (!BigIntSqrt(Bsq).Pow(2).Equals(Bsq) && XsubY_prev.Subtract(XsubY).CompareTo(c) > -1)
            {
                x = x.Add(BigInteger.One);
                Bsq = x.Multiply(x).Subtract(n);

                y = BigIntSqrt(Bsq);
                XsubY_prev = XsubY;
                XsubY = x.Subtract(y);
            }

            if (BigIntSqrt(Bsq).Pow(2).Equals(Bsq))
            {
                result = XsubY;
            }
            
            // Trial Division
            else
            {
                bool solved = false;
                BigInteger p = XsubY.Add(BigInteger.Two);

                if (p.Remainder(BigInteger.Two).IntValue == 0)
                {
                    p = p.Add(BigInteger.One);
                }
                while (!solved)
                {
                    p = p.Subtract(BigInteger.Two);
                    if (n.Remainder(p).Equals(BigInteger.Zero))
                    {
                        solved = true;
                    }
                }

                result = p;
            }*/
            #endregion

            BigInteger result = BigInteger.Zero;
            //BigInteger x = BigIntSqrt(n).Add(BigInteger.One);
            BigInteger x = BigIntSqrt(n);
            BigInteger k = BigInteger.One;
            BigInteger y = x.Add(k).Pow(2).Subtract(n);
            BigInteger ysq = BigIntSqrt(y);
            BigInteger temp = BigInteger.Zero;

            while (!ysq.Pow(2).Equals(y))
            {
                k = k.Add(BigInteger.One);
                y = (x.Add(k)).Square().Subtract(n);
                ysq = BigIntSqrt(y);
            }

            if (ysq.Pow(2).Equals(y))
            {
                temp = x.Add(k);
                result = temp.Subtract(ysq);
            }

            return new Tuple<BigInteger, BigInteger>(result, n.Divide(result));
        }
        
        // атака методом Винера
        static BigInteger WienerAttack(BigInteger E, BigInteger N, BigInteger msg)
        {
            List<Convergent> convergents = new List<Convergent>(10000000);
            List<BigInteger> contfrac = new List<BigInteger>(10000000);
            bool check = false;
            BigInteger result = BigInteger.Zero;

            /*BigInteger isE = new BigInteger("6792605526025");
            BigInteger isN = new BigInteger("9449868410449");
            BigInteger myM = new BigInteger("16843009"); // 0x01010101*/
            BigInteger isE = E;
            BigInteger isN = N;
            BigInteger myM = msg;
            BigInteger limitD = BigIntSqrt(BigIntSqrt(isN)).Divide(BigInteger.Three);

            GenConvergentList(contfrac, convergents, isE, isN);

            for (int i = 0; i < convergents.Count(); i++)
            {
                if (convergents[i].d.CompareTo(limitD) == 1)
                    break;

                BigInteger isC = myM.ModPow(isE, isN);
                BigInteger myM2 = isC.ModPow(convergents[i].d, isN);

                if (myM.Equals(myM2))
                {
                    Console.WriteLine("{0}/{1}: {2}: true",
                        convergents[i].n, convergents[i].d, limitD);
                    return new BigInteger(Convert.ToString(convergents[i].d));
                }
                else
                {
                    Console.WriteLine("{0}/{1}: {2}: false",
                        convergents[i].n, convergents[i].d, limitD);
                }
            }
            return result;
        }
        // создание цепной дроби
        static void GenConvergentList(List<BigInteger> contfrac, List<Convergent> convergents, BigInteger E, BigInteger N)
        {
            BigInteger temp = BigInteger.Zero;
            BigInteger r = BigInteger.Zero;
            BigInteger s = BigInteger.One;
            BigInteger p = BigInteger.One;
            BigInteger q = BigInteger.Zero;

            BigInteger r_temp;
            BigInteger s_temp;
            BigInteger p_temp;
            BigInteger q_temp;

            BigInteger n;
            while (!N.Equals(BigInteger.Zero))
            {
                n = E.Divide(N);
                temp = E.Subtract(N.Multiply(n));
                E = N;
                N = temp;
                contfrac.Add(n);
                //contfrac.Add(Convert.ToInt32(n.ToString());
            }

            foreach (var c in contfrac)
            {
                r_temp = r; s_temp = s; p_temp = p; q_temp = q;
                r = p_temp; s = q_temp;
                p = c.Multiply(p_temp).Add(r_temp);
                q = c.Multiply(q_temp).Add(s_temp);
                convergents.Add(new Convergent(p, q));
            }
        }

        class Convergent
        {
            // numerator - числитель
            // denominator - знаменатель
            //int n, d;
            public Convergent(BigInteger numerator, BigInteger denominator)
            {
                n = numerator;
                d = denominator;
            }
            public BigInteger n { get; set; }
            public BigInteger d { get; set; }

        }

        // атака повторным шифрованием
        static Tuple<BigInteger, BigInteger> ReplayAttach(BigInteger N, BigInteger e, BigInteger y)
        {
            BigInteger ymain = y;
            BigInteger m = BigInteger.Zero;

            BigInteger yprev = y;

            do
            {
                yprev = y;
                y = y.ModPow(e, N);
                m = m.Add(BigInteger.One);
                Console.SetCursorPosition(0, Console.CursorTop);
                Console.Write("m = " + m);
            }
            while (ymain.CompareTo(y) != 0);

            return new Tuple<BigInteger, BigInteger>(yprev, m);
        }

        // атака посредством метода бесключевого чтения
        static BigInteger KeylessAttack(BigInteger N, BigInteger e1, BigInteger e2, BigInteger x)
        {
            BigInteger y1 = x.ModPow(e1, N);
            BigInteger y2 = x.ModPow(e2, N);
            BigInteger d = BigInteger.Zero;

            var r_s = EGCD(e1, e2, d);

            return y1.ModPow(r_s.Item1, N).Multiply(y2.ModPow(r_s.Item2, N)).Mod(N);
        }

        // расширенный алгоритм Евклида
        static Tuple<BigInteger, BigInteger> EGCD(BigInteger a, BigInteger b, BigInteger d)
        {
            BigInteger x, y;
            BigInteger q, r, x1, x2, y1, y2;
            if (b.Equals(BigInteger.Zero))
            {
                d = a; x = BigInteger.One; y = BigInteger.Zero;
                return new Tuple<BigInteger, BigInteger>(x, y);
            }

            x2 = BigInteger.One;
            x1 = BigInteger.Zero;
            y2 = BigInteger.Zero;
            y1 = BigInteger.One;
            
            while (b.CompareTo(BigInteger.Zero) == 1)
            {
                q = a.Divide(b);
                r = a.Subtract(q.Multiply(b));

                x = x2.Subtract(q.Multiply(x1));
                y = y2.Subtract(q.Multiply(y1));

                a = b;
                b = r;

                x2 = x1;
                x1 = x;
                y2 = y1;
                y1 = y;
            }

            d = a;
            x = x2;
            y = y2;

            return new Tuple<BigInteger, BigInteger>(x, y);
        }

        // sqrt
        static BigInteger BigIntSqrt(BigInteger N)
        {
            BigInteger G = new BigInteger((N.ShiftRight((N.BitLength + 1) / 2)).ToString());
            BigInteger LastG = null;
            do
            {
                LastG = G;
                G = N.Divide(G).Add(G).ShiftRight(1);
            }
            while (!(G.Xor(LastG).ToString() == "0"));
            return G;
        }

        #region enc/dec
        static void BytesToList(int blocklength, byte[] data, List<BigInteger> cur_data)
        {
            cur_data.Clear();
            for (int i = 0; i < data.Count(); i += blocklength)
            {
                byte[] temp = new byte[blocklength];
                for (int j = 0; j < blocklength; j++)
                {
                    if (i + j >= data.Count())
                        temp[j] = 0;
                    else
                        temp[j] = data[i + j];
                }
                cur_data.Add(new BigInteger(temp));
                //k++;
            }
        }
        static void EncodeText(CustomRSA Key, List<BigInteger> cur_data, List<BigInteger> enc_data)
        {
            enc_data.Clear();
            for (int i = 0; i < cur_data.Count(); i++)
                enc_data.Add(cur_data[i].ModPow(Key.E, Key.N));
        }
        static void DecodeText(CustomRSA Key, List<BigInteger> enc_data, List<BigInteger> dec_data)
        {
            dec_data.Clear();
            for (int i = 0; i < enc_data.Count(); i++)
                dec_data.Add(enc_data[i].ModPow(Key.D, Key.N));
        }
        static void DecodeTextOptimized(CustomRSA Key, List<BigInteger> enc_data, List<BigInteger> dec_data)
        {
            BigInteger m0 = BigInteger.Zero;
            BigInteger m1 = BigInteger.Zero;
            BigInteger m2 = BigInteger.Zero;
            BigInteger h = BigInteger.Zero;

            dec_data.Clear();
            for (int i = 0; i < enc_data.Count(); i++)
            {
                m1 = enc_data[i].ModPow(Key.DP, Key.P);
                m2 = enc_data[i].ModPow(Key.DQ, Key.Q);
                h = Key.QINV.Multiply(m1.Subtract(m2)).Mod(Key.P);
                m0 = m2.Add(h.Multiply(Key.Q));

                dec_data.Add(m0);
            }
        }

        static void DoAllTheJobWithText(
            string text, CustomRSA Key,
            List<BigInteger> cur_data,
            List<BigInteger> enc_data,
            List<BigInteger> dec_data)
        {
            int blocklength = Key.KeyLength / 8;
            byte[] data = ENC.GetBytes(text);
            BytesToList(blocklength, data, cur_data);

            w("\n\n текущий текст: ");
            WriteList(cur_data, blocklength);

            EncodeText(Key, cur_data, enc_data);
            w("\n\n encoded текст: ");
            WriteListBASE64(enc_data, blocklength);

            /*DecodeText(Key, enc_data, dec_data);
            w("\n\n non-optimized: ");
            WriteList(dec_data, blocklength);*/

            DecodeTextOptimized(Key, enc_data, dec_data);
            w("\n\n     optimized: ");
            WriteList(dec_data, blocklength);
        }
        #endregion

        #region some useful functions
        static void AddElapsedTime(string v, List<ElapsedTime> list, Stopwatch stopwatch)
        {
            stopwatch.Stop();
            list.Add(new ElapsedTime(v, stopwatch.Elapsed));
            stopwatch.Reset();
        }

        static void w(object s)
        {
            Console.Write(s.ToString());
        }
        static void wl(object s)
        {
            Console.WriteLine(s.ToString());
        }
        static void ri(ref int o)
        {
            o = Convert.ToInt32(Console.ReadLine());
        }
        static void rs(ref string o)
        {
            o = Console.ReadLine();
        }
        static string rs()
        {
            return Console.ReadLine();
        }
        static void s(int time)
        {
            System.Threading.Thread.Sleep(time);
        }

        static void showTimeElapsed(List<ElapsedTime> list)
        {
            Console.WriteLine("\n\n Тайминги:");
            foreach (ElapsedTime v in list)
                Console.WriteLine(" " + v.Info + ":\t" + v.Time);
            //v.Time.Seconds + ":" + v.Time.Milliseconds);
        }

        static void WriteList(List<BigInteger> data, int blocklength)
        {
            for (int i = 0; i < data.Count(); i++)
                w(ENC.GetString(data[i].ToByteArray()));
        }
        static void WriteListBytes(List<BigInteger> data, int blocklength)
        {
            for (int i = 0; i < data.Count(); i++)
                w(BitConverter.ToString(data[i].ToByteArray()));
        }
        static void WriteListBASE64(List<BigInteger> data, int blocklength)
        {
            for (int i = 0; i < data.Count(); i++)
                w(Convert.ToBase64String(data[i].ToByteArray()));
        }
        #endregion
    }
}
