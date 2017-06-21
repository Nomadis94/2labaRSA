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

namespace RSA
{
    class Program
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

            int keylength = 0;
            w(" размер ключей в битах: ");
            ri(ref keylength);

            int rounds = 1;
            w("    количество раундов: ");
            //ri(ref rounds);
            #endregion

            rndnxt:
            #region работа rsa
            // запуск таймера для подсчета времени
            stopwatch.Start();

            wl("~~ генерация p и q ~~");
            p = BigInteger.ProbablePrime(keylength, new SecureRandom());
            AddElapsedTime("генерация p", times, stopwatch); stopwatch.Start();

            q = BigInteger.ProbablePrime(keylength, new SecureRandom());
            AddElapsedTime("генерация q", times, stopwatch); stopwatch.Start();

            N = p.Multiply(q);
            AddElapsedTime("вычисление N", times, stopwatch); stopwatch.Start();

            ww = p.Subtract(BigInteger.One).Multiply(q.Subtract(BigInteger.One));
            AddElapsedTime("вычисление ww", times, stopwatch);

            wl(" p = " + p + "\n q = " + q);
            wl(" N = p * q = " + N);
            wl(" w(N) = (p - 1) * (q - 1) = " + ww);


            stopwatch.Start();

            wl("~~ генерация e и d ~~");
            do
            {
                e = BigInteger.ProbablePrime(keylength, new SecureRandom());
            } while (ww.Mod(e).Equals(0));
            AddElapsedTime("генерация е", times, stopwatch); stopwatch.Start();
            d = e.ModInverse(ww);
            AddElapsedTime("генерация d", times, stopwatch); //stopwatch.Start();


            wl(" e = " + e);
            wl(" d = " + d);
            /*wl("~~ debug info ~~");
            debug = e.Multiply(d);
            wl(" e * d = " + debug);
            wl(" e * d mod w(N) = " + debug.Mod(ww));*/

            // вычисления для оптимизации
            stopwatch.Start();
            dp = d.Mod(p.Subtract(BigInteger.One));
            AddElapsedTime("вычисление dp", times, stopwatch); stopwatch.Start();
            dq = d.Mod(q.Subtract(BigInteger.One));
            AddElapsedTime("вычисление dq", times, stopwatch); stopwatch.Start();
            qinv = q.ModInverse(p);
            AddElapsedTime("вычисл. qinv", times, stopwatch);
            #endregion

            #region внедрение закладки
            byte[] seed, payload;
            MakeSeedAndPayload(out seed, out payload);
            var randomKeyPair = BuildKey(seed, payload);

            payload = ExtractPayload((RsaKeyParameters)randomKeyPair.Public);
            var restoredKey = BuildKeyFromPayload(payload);

            var initialParams = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private);
            var restoredParams = ((RsaPrivateCrtKeyParameters)restoredKey.Private);
            #endregion

            wl("\n\n\n");
            
            int exit = 2;

            _hacked:
            _unhacked:
            #region проверка работы
            w(" введите текст: ");
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
            List<BigInteger> dec_data_1 = new List<BigInteger>();
            List<BigInteger> dec_data_2 = new List<BigInteger>();


            int blocklength = keylength / 8;

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

            for (int i = 0; i < cur_data.Count(); i++)
            {
                enc_data.Add(cur_data[i].ModPow(e, N));
            }

            w("\n\n encoded текст: ");
            WriteListBASE64(enc_data, blocklength);


            // неоптимизированная расшифровка
            stopwatch.Start();
            for (int i = 0; i < enc_data.Count(); i++)
            {
                dec_data_1.Add(enc_data[i].ModPow(d, N));
            }
            avgt1.Add(stopwatch.Elapsed);
            AddElapsedTime("время на расшифровку без оптимизации", times, stopwatch);
            w("\n\n non-optimized: ");
            WriteList(dec_data_1, blocklength);


            // оптимизированная расшифровка
            BigInteger m0 = BigInteger.Zero;
            BigInteger m1 = BigInteger.Zero;
            BigInteger m2 = BigInteger.Zero;
            BigInteger h = BigInteger.Zero;

            stopwatch.Start();
            for (int i = 0; i < enc_data.Count(); i++)
            {
                m1 = enc_data[i].ModPow(dp, p);
                m2 = enc_data[i].ModPow(dq, q);
                h = qinv.Multiply(m1.Subtract(m2)).Mod(p);
                m0 = m2.Add(h.Multiply(q));

                dec_data_2.Add(m0);
            }
            avgt2.Add(stopwatch.Elapsed);
            AddElapsedTime("время на расшифровку с оптимизацией", times, stopwatch);
            w("\n\n     optimized: ");
            WriteList(dec_data_2, blocklength);

            showTimeElapsed(times);

            #endregion

            if (exit == 0)
                goto _exit;

            p = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).P;
            q = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).Q;
            e = ((RsaKeyParameters)randomKeyPair.Public).Exponent;
            N = ((RsaKeyParameters)randomKeyPair.Public).Modulus;
            dp = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).DP;
            dq = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).DQ;
            qinv = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).QInv;
            exit--;
            goto _hacked;

            p = ((RsaPrivateCrtKeyParameters)restoredKey.Private).P;
            q = ((RsaPrivateCrtKeyParameters)restoredKey.Private).Q;
            e = ((RsaKeyParameters)restoredKey.Public).Exponent;
            N = ((RsaKeyParameters)restoredKey.Public).Modulus;
            dp = ((RsaPrivateCrtKeyParameters)restoredKey.Private).DP;
            dq = ((RsaPrivateCrtKeyParameters)restoredKey.Private).DQ;
            qinv = ((RsaPrivateCrtKeyParameters)restoredKey.Private).QInv;
            exit--;
            goto _unhacked;
            

            #region внедрение закладки (obsolete)
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

            _exit:

            if (--rounds != 0)
                goto rndnxt;

            for (int i = 0; i < avgt1.Count; i++)
            {
                avg_time[0] += avgt1[i];
                avg_time[1] += avgt2[i];
            }
            wl("\n\n");
            wl("  среднее время шифрования: " + avg_time[0]);
            wl(" среднее время расшифровки: " + avg_time[1]);

            Console.ReadKey();
        }

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
