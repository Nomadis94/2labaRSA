using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.Security;
using Org.BouncyCastle.Crypto;
using Org.BouncyCastle.Crypto.Parameters;
using Chaos.NaCl;
using Org.BouncyCastle.Crypto.Generators;
using RSA.Backdoor;
using System.Threading;

namespace RSA
{
    class RsaBackdoor
    {
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
    }
    class CustomRSA
    {
        BigInteger p, q;
        BigInteger n;
        BigInteger ww;
        BigInteger e, d;
        BigInteger dp, dq, qinv;
        int length = 32;    // by default

        AsymmetricCipherKeyPair key;

        public CustomRSA()
        {
            p = BigInteger.Zero;
            q = BigInteger.Zero;
            n = BigInteger.Zero;
            ww = BigInteger.Zero;
            e = BigInteger.Zero;
            d = BigInteger.Zero;
            dp = BigInteger.Zero;
            dq = BigInteger.Zero;
            qinv = BigInteger.Zero;
        }
        public CustomRSA(int _length)
        {
            p = BigInteger.Zero;
            q = BigInteger.Zero;
            n = BigInteger.Zero;
            ww = BigInteger.Zero;
            e = BigInteger.Zero;
            d = BigInteger.Zero;
            dp = BigInteger.Zero;
            dq = BigInteger.Zero;
            qinv = BigInteger.Zero;
            length = _length;
        }
        public CustomRSA(AsymmetricCipherKeyPair keyPair)
        {
            p = ((RsaPrivateCrtKeyParameters)keyPair.Private).P;
            q = ((RsaPrivateCrtKeyParameters)keyPair.Private).Q;
            e = ((RsaKeyParameters)keyPair.Public).Exponent;
            n = ((RsaKeyParameters)keyPair.Public).Modulus;
            dp = ((RsaPrivateCrtKeyParameters)keyPair.Private).DP;
            dq = ((RsaPrivateCrtKeyParameters)keyPair.Private).DQ;
            qinv = ((RsaPrivateCrtKeyParameters)keyPair.Private).QInv;
            length = 32;
        }
        public CustomRSA(AsymmetricCipherKeyPair keyPair, int _length)
        {
            p = ((RsaPrivateCrtKeyParameters)keyPair.Private).P;
            q = ((RsaPrivateCrtKeyParameters)keyPair.Private).Q;
            e = ((RsaKeyParameters)keyPair.Public).Exponent;
            n = ((RsaKeyParameters)keyPair.Public).Modulus;
            dp = ((RsaPrivateCrtKeyParameters)keyPair.Private).DP;
            dq = ((RsaPrivateCrtKeyParameters)keyPair.Private).DQ;
            qinv = ((RsaPrivateCrtKeyParameters)keyPair.Private).QInv;
            length = _length;
        }

        // сгенерировать все параметры (p, q, N, w(N), e, d)
        // а также параметры для оптимизации (dp, dq, qinv)
        public void GenParams()
        {
            p = BigInteger.ProbablePrime(length, new SecureRandom());
            q = BigInteger.ProbablePrime(length, new SecureRandom());
            n = p.Multiply(q);
            ww = p.Subtract(BigInteger.One).Multiply(q.Subtract(BigInteger.One));
            do
            {
                e = BigInteger.ProbablePrime(length, new SecureRandom());
            } while (ww.Mod(e).Equals(0));
            d = e.ModInverse(ww);

            // вычисления для оптимизации
            dp = d.Mod(p.Subtract(BigInteger.One));
            dq = d.Mod(q.Subtract(BigInteger.One));
            qinv = q.ModInverse(p);
            
            /*Thread thread;
            thread = new Thread(ThreadGenParams);
            thread.Start("p");
            thread = new Thread(ThreadGenParams);
            thread.Start("q");

            thread.Suspend();
            n = p.Multiply(q);

            thread = new Thread(ThreadGenParams);
            thread.Start("ww");
            thread.Suspend();
            do
            {
                e = BigInteger.ProbablePrime(length, new SecureRandom());
            } while (ww.Mod(e).Equals(0));
            thread.Suspend();
            d = e.ModInverse(ww);

            thread = new Thread(ThreadGenParams);
            thread.Start("dp");
            thread = new Thread(ThreadGenParams);
            thread.Start("dq");
            thread = new Thread(ThreadGenParams);
            thread.Start("qinv");
            while (dp == null || dq == null || qinv == null) {; }
            Console.Write("done");*/
        }

        // распараллеливание
        public void ThreadGenParams(object v)
        {
            switch ((string)v)
            {
                case "p":
                    p = BigInteger.ProbablePrime(length, new SecureRandom());
                    break;
                case "q":
                    q = BigInteger.ProbablePrime(length, new SecureRandom());
                    break;
                case "n":
                    n = p.Multiply(q);
                    break;
                case "ww":
                    ww = p.Subtract(BigInteger.One).Multiply(q.Subtract(BigInteger.One));
                    break;
                case "e":
                    do
                    {
                        e = BigInteger.ProbablePrime(length, new SecureRandom());
                    } while (ww.Mod(e).Equals(0));
                    break;
                case "d":
                    d = e.ModInverse(ww);
                    break;
                case "dp":
                    dp = d.Mod(p.Subtract(BigInteger.One));
                    break;
                case "dq":
                    dq = d.Mod(q.Subtract(BigInteger.One));
                    break;
                case "qinv":
                    qinv = q.ModInverse(p);
                    break;
                default:
                    break;
            }
        }

        // внедрить бекдор
        public void InsertBackdoor()
        {
            byte[] seed, payload;
            RsaBackdoor.MakeSeedAndPayload(out seed, out payload);
            var randomKeyPair = RsaBackdoor.BuildKey(seed, payload);

            key = randomKeyPair;
            e = ((RsaKeyParameters)randomKeyPair.Public).Exponent;
            N = ((RsaKeyParameters)randomKeyPair.Public).Modulus;
            p = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).P;
            q = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).Q;
            dp = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).DP;
            dq = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).DQ;
            qinv = ((RsaPrivateCrtKeyParameters)randomKeyPair.Private).QInv;
        }

        // получить ключи с помощью бекдора
        public void ExtractKeysFromBackdoor(RsaKeyParameters _key)
        {
            //RsaKeyParameters _key = new RsaKeyParameters(false, N, e);
            byte[] payload = RsaBackdoor.ExtractPayload(_key);
            var restoredKey = RsaBackdoor.BuildKeyFromPayload(payload);

            e = ((RsaKeyParameters)restoredKey.Public).Exponent;
            N = ((RsaKeyParameters)restoredKey.Public).Modulus;
            p = ((RsaPrivateCrtKeyParameters)restoredKey.Private).P;
            q = ((RsaPrivateCrtKeyParameters)restoredKey.Private).Q;
            dp = ((RsaPrivateCrtKeyParameters)restoredKey.Private).DP;
            dq = ((RsaPrivateCrtKeyParameters)restoredKey.Private).DQ;
            qinv = ((RsaPrivateCrtKeyParameters)restoredKey.Private).QInv;
        }

        public int KeyLength { get { return length; } set { } }
        public BigInteger E { get { return e; } set { e = value; } }
        public BigInteger N { get { return n; } set { n = value; } }
        public BigInteger D { get { return d; } set { d = value; } }
        public BigInteger WW { get { return ww; } set { ww = value; } }

        public BigInteger P { get { return p; } set { p = value; } }
        public BigInteger Q { get { return q; } set { q = value; } }
        public BigInteger DP { get { return dp; } set { dp = value; } }
        public BigInteger DQ { get { return dq; } set { dq = value; } }
        public BigInteger QINV { get { return qinv; } set { qinv = value; } }

        /*public byte[] encoding(byte[] bytes)
        {
        	return 0;
        }*/
    }
}
