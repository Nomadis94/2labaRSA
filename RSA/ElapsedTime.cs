using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace RSA
{
    class ElapsedTime
    {
        string info;
        TimeSpan time;

        public ElapsedTime()
        {
            info = " ?: ";
            time = DateTime.Now.TimeOfDay;
        }

        public ElapsedTime(string v, TimeSpan t)
        {
            info = v;
            time = t;
        }

        public string Info { get { return info; } }
        public TimeSpan Time { get { return time; } }
    }
}
