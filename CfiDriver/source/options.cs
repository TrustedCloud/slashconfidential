using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CfiDriver
{
    public static class Options
    {
        public static int timeoutPerProcess = 1200;
        public static bool IsLinux()
        {
            int p = (int)Environment.OSVersion.Platform;
            return (p == 4) || (p == 6) || (p == 128); //4 is for UNIX, 6 is for Mac, 128 for older Mono
        }

        public static List<Tuple<string, string, string, string>> CollectTimeoutAggregateBenchmarks()
        {
            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            //commening out > 50% of each set to get a primary run
            var dirs = new List<string>()  {
                @"benchmarks"+s+"AggregateTask"+s+"func_0000000000002770" 
                ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000003760" 
                ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000003A00" 
            };

            var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:1880 /funcGuardCheckIcallCfw:5210 /funcMemset:3aa0 /funcMemcpy:3cf0 /funcMemcmp:3fc0 /funcSGXMalloc:50e0 /funcSGXFree:50e6 /dataLow:7000 /dataHigh:74df", "baseline")
            };

            //cross product
            return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectAggregateBenchmarks()
        {
          var bplFile = @"dll_func.bpl";
          var s = IsLinux() ? @"/" : @"\";

          //commening out > 50% of each set to get a primary run
          var dirs = new List<string>()  {
               //  @"benchmarks"+s+"AggregateTask"+s+"func_0000000000001370"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001600"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001880"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001890"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_00000000000018B0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_00000000000018C0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000003750"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000005260"
               // //,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000005280" //_guard_init_region should not be part of U
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000005350"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000005360"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001000"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_00000000000010B0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001110"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001170"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001350"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001360"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001390"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001430"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001460"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_00000000000014D0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001610"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001680"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_00000000000016F0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001700"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001850"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_00000000000018A0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_00000000000018D0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001930"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001AC0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001B20"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000001B30"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000002770" 
                @"benchmarks"+s+"AggregateTask"+s+"func_0000000000003760" 
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000003950"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_00000000000039F0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000003A00" 
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000003CD0"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000004A90"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000004C10"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000004D80" 
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000005210"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000005270"
               // ,@"benchmarks"+s+"AggregateTask"+s+"func_0000000000005410"
            };

          var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:1880 /funcGuardCheckIcallCfw:5210 /funcMemset:3aa0 /funcMemcpy:3cf0 /funcMemcmp:3fc0 /funcSGXMalloc:50e0 /funcSGXFree:50e6 /dataLow:7000 /dataHigh:74df", "baseline")
            };

          //cross product
          return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectTimeoutLbmBenchmarks()
        {
            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            //commening out > 50% of each set to get a primary run
            var dirs = new List<string>()  {
                @"benchmarks" + s + "lbm" +s+ "main" +s+ "func_0000000000000000"
            };

            var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2f60 /funcGuardCheckIcallCfw:50d0 /funcMemset:3960 /funcMemcpy:3bb0 /funcMemcmp:3e80 /funcSGXMalloc:4fa0 /funcSGXFree:4fa6 /dataLow:7000 /dataHigh:71ef /disablePolicyChecking+", "baseline")
            };

            //cross product
            return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectLbmBenchmarks()
        {
            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            //commening out > 50% of each set to get a primary run
            var dirs = new List<string>()  {
                 @"benchmarks" + s + "lbm" +s+ "lbm" +s+ "func_0000000000008D90"
                ,@"benchmarks" + s + "lbm" +s+ "lbm" +s+ "func_0000000000000C40"
                ,@"benchmarks" + s + "lbm" +s+ "lbm" +s+ "func_0000000000000F70"
                ,@"benchmarks" + s + "lbm" +s+ "lbm" +s+ "func_0000000000000A50"
                ,@"benchmarks" + s + "lbm" +s+ "lbm" +s+ "func_0000000000000D90"
                ,@"benchmarks" + s + "lbm" +s+ "lbm" +s+ "func_0000000000008B90"
                ,@"benchmarks" + s + "lbm" +s+ "lbm" +s+ "func_0000000000000130"
                ,@"benchmarks" + s + "lbm" +s+ "main" +s+ "func_0000000000000960"
                ,@"benchmarks" + s + "lbm" +s+ "main" +s+ "func_00000000000007D0"
                ,@"benchmarks" + s + "lbm" +s+ "main" +s+ "func_0000000000000000"
                ,@"benchmarks" + s + "lbm" +s+ "main" +s+ "func_00000000000008A0"
                ,@"benchmarks" + s + "lbm" +s+ "main" +s+ "func_0000000000000930"
            };

            var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2f60 /funcGuardCheckIcallCfw:50d0 /funcMemset:3960 /funcMemcpy:3bb0 /funcMemcmp:3e80 /funcSGXMalloc:4fa0 /funcSGXFree:4fa6 /dataLow:7000 /dataHigh:71ef /disablePolicyChecking+", "baseline")
            };

            //cross product
            return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectTimeoutAStarBenchmarks()
        {
            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            //commening out > 50% of each set to get a primary run
            var dirs = new List<string>()  {
                @"benchmarks" + s + "astar" +s+ "RegBounds" +s+ "func_0000000000000000"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_00000000000000D0"
            };

            var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2f60 /funcGuardCheckIcallCfw:50d0 /funcMemset:3960 /funcMemcpy:3bb0 /funcMemcmp:3e80 /funcSGXMalloc:4fa0 /funcSGXFree:4fa6 /dataLow:7000 /dataHigh:71ef /disablePolicyChecking+", "baseline")
            };

            //cross product
            return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectAStarBenchmarks()
        {
            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            //commening out > 50% of each set to get a primary run
            var dirs = new List<string>()  {
                 //@"benchmarks" + s + "astar" +s+ "CreateWay" +s+ "func_0000000000000E00" //BAP seems to decompile incorrectly
                 @"benchmarks" + s + "astar" +s+ "CreateWay" +s+ "func_0000000000003000"
                ,@"benchmarks" + s + "astar" +s+ "CreateWay" +s+ "func_00000000000030B0"
                ,@"benchmarks" + s + "astar" +s+ "CreateWay" +s+ "func_00000000000048E0"
                ,@"benchmarks" + s + "astar" +s+ "Library" +s+ "func_0000000000000000"
                ,@"benchmarks" + s + "astar" +s+ "Places" +s+ "func_0000000000000C50"
                ,@"benchmarks" + s + "astar" +s+ "Random" +s+ "func_00000000000001C0"
                ,@"benchmarks" + s + "astar" +s+ "RegBounds" +s+ "func_0000000000000000"
                ,@"benchmarks" + s + "astar" +s+ "RegBounds" +s+ "func_0000000000000380"
                ,@"benchmarks" + s + "astar" +s+ "RegBounds" +s+ "func_0000000000000520"
                ,@"benchmarks" + s + "astar" +s+ "RegBounds" +s+ "func_0000000000001080"
                //,@"benchmarks" + s + "astar" +s+ "RegBounds" +s+ "func_0000000000001200" //Graph exception
                ,@"benchmarks" + s + "astar" +s+ "RegBounds" +s+ "func_0000000000001410"
                ,@"benchmarks" + s + "astar" +s+ "RegBounds" +s+ "func_0000000000001C80"
                //,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_0000000000000000" //Graph exception
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_00000000000000D0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_00000000000002B0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_0000000000000BE0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_0000000000000CA0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_0000000000000DA0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_00000000000012D0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_00000000000016D0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_0000000000001E50"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_00000000000020A0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_00000000000029A0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_0000000000002FF0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_00000000000034B0"
                ,@"benchmarks" + s + "astar" +s+ "RegMng" +s+ "func_0000000000003630"
                ,@"benchmarks" + s + "astar" +s+ "Region" +s+ "func_00000000000002F0"
                ,@"benchmarks" + s + "astar" +s+ "Region" +s+ "func_0000000000000490"
                ,@"benchmarks" + s + "astar" +s+ "Region" +s+ "func_00000000000008A0"
                ,@"benchmarks" + s + "astar" +s+ "Region" +s+ "func_0000000000000920"
                ,@"benchmarks" + s + "astar" +s+ "Way" +s+ "func_0000000000000000"
                //,@"benchmarks" + s + "astar" +s+ "Way" +s+ "func_0000000000000290" //Boogie out of memory
                ,@"benchmarks" + s + "astar" +s+ "Way" +s+ "func_0000000000001520"
                //,@"benchmarks" + s + "astar" +s+ "Way" +s+ "func_0000000000001A70" //Boogie out of memory.=
                ,@"benchmarks" + s + "astar" +s+ "Way" +s+ "func_0000000000003130"
                //,@"benchmarks" + s + "astar" +s+ "Way2" +s+ "func_0000000000000000" //Graph exception
                ,@"benchmarks" + s + "astar" +s+ "Way2" +s+ "func_00000000000001C0"
                ,@"benchmarks" + s + "astar" +s+ "Way2" +s+ "func_0000000000000690"
                ,@"benchmarks" + s + "astar" +s+ "Way2" +s+ "func_0000000000000EA0"
                ,@"benchmarks" + s + "astar" +s+ "Way2" +s+ "func_00000000000017C0"
                ,@"benchmarks" + s + "astar" +s+ "Way2" +s+ "func_0000000000001C50"
                ,@"benchmarks" + s + "astar" +s+ "Way2" +s+ "func_0000000000002170"
                ,@"benchmarks" + s + "astar" +s+ "Way2" +s+ "func_0000000000002500"
                ,@"benchmarks" + s + "astar" +s+ "Way2" +s+ "func_00000000000025C0"
                ,@"benchmarks" + s + "astar" +s+ "WayInit" +s+ "func_0000000000000A20"
                ,@"benchmarks" + s + "astar" +s+ "WayInit" +s+ "func_0000000000000B10"
                ,@"benchmarks" + s + "astar" +s+ "WayInit" +s+ "func_0000000000000C00"
                ,@"benchmarks" + s + "astar" +s+ "WayInit" +s+ "func_00000000000023D0"
                ,@"benchmarks" + s + "astar" +s+ "WayInit" +s+ "func_00000000000023E0"
            };

            var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2f60 /funcGuardCheckIcallCfw:50d0 /funcMemset:3960 /funcMemcpy:3bb0 /funcMemcmp:3e80 /funcSGXMalloc:4fa0 /funcSGXFree:4fa6 /dataLow:7000 /dataHigh:71ef /disablePolicyChecking+", "baseline")
            };

            //cross product
            return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectTimeoutBzip2Benchmarks()
        {
            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            //commening out > 50% of each set to get a primary run
            var dirs = new List<string>()  {
                     @"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000005900"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000000000"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000001390"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000002B10"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000003C90"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006700"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000002D90"
                    ,@"benchmarks" + s + "bzip2" +s+ "compress" +s+ "func_0000000000000000"
            };

            var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2f60 /funcGuardCheckIcallCfw:50d0 /funcMemset:3960 /funcMemcpy:3bb0 /funcMemcmp:3e80 /funcSGXMalloc:4fa0 /funcSGXFree:4fa6 /dataLow:7000 /dataHigh:71ef /disablePolicyChecking+", "baseline")
            };

            //cross product
            return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectBzip2Benchmarks()
        {
            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            //commening out > 50% of each set to get a primary run
            var dirs = new List<string>()  {
                     @"benchmarks"+s+"bzip2"+s+"blocksort"+s+"func_0000000000000500"
                    ,@"benchmarks"+s+"bzip2"+s+"blocksort"+s+"func_0000000000002B90"
                    ,@"benchmarks"+s+"bzip2"+s+"blocksort"+s+"func_0000000000003890"
                    ,@"benchmarks"+s+"bzip2"+s+"blocksort"+s+"func_0000000000003E90"
                    //,@"benchmarks"+s+"bzip2"+s+"blocksort"+s+"func_0000000000003F20" //boogie out of mem
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_00000000000000A0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000000120"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_00000000000000E0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000000000"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000000170"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000001750"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000001770"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_00000000000017B0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_00000000000001A0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000000A50"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000000200"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000000610"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000000740"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzip2" +s+ "func_0000000000000050"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000001EE0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000005900"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_00000000000011F0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006330"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000001B00"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000008750"
                    //,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006D80" //graph exception
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000000000"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000001390"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006A80"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000004540"
                    //,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000000D80" //graph exception
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_000000000000DEB0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_000000000000DEF0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000003150"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006900"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006A50"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000007970"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000008A30"
                    //,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000008CE0" //graph exception
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000002B10"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006CC0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000002090"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_00000000000069E0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006300"
                    //,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_000000000000B240" //graph exception
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_00000000000079B0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006970"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000003C90"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006DB0"
                    //,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000005DD0" //graph exception
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_00000000000066F0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006700"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000004E50"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006A10"
                    //,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006360" //graph exception
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000004DF0"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006870"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000002D90"
                    ,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_00000000000062F0"
                    //,@"benchmarks" + s + "bzip2" +s+ "bzlib" +s+ "func_0000000000006570" //graph exception
                    ,@"benchmarks"+s+"bzip2"+s+"compress"+s+"func_0000000000000000"
                    ,@"benchmarks"+s+"bzip2"+s+"compress"+s+"func_00000000000004F0"
                    ,@"benchmarks"+s+"bzip2"+s+"compress"+s+"func_00000000000005B0"
                    ,@"benchmarks"+s+"bzip2"+s+"compress"+s+"func_0000000000000780"
                    ,@"benchmarks"+s+"bzip2"+s+"compress"+s+"func_0000000000000A40"
                    ,@"benchmarks"+s+"bzip2"+s+"compress"+s+"func_0000000000000AD0"
                    ,@"benchmarks"+s+"bzip2"+s+"compress"+s+"func_0000000000000B00"
                    ,@"benchmarks" + s + "bzip2" +s+ "decompress" +s+ "func_0000000000012C10"
                    ,@"benchmarks" + s + "bzip2" +s+ "huffman" +s+ "func_00000000000014C0"
                    ,@"benchmarks" + s + "bzip2" +s+ "huffman" +s+ "func_0000000000000000"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000001470"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_00000000000016E0"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000000000"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000000070"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000000F10"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000000A10"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000000D40"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_00000000000005E0"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000000C20"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000001090"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000000030"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_00000000000000B0"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_00000000000018C0"
                    ,@"benchmarks" + s + "bzip2" +s+ "spec" +s+ "func_0000000000001660"
            };

            var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2f60 /funcGuardCheckIcallCfw:50d0 /funcMemset:3960 /funcMemcpy:3bb0 /funcMemcmp:3e80 /funcSGXMalloc:4fa0 /funcSGXFree:4fa6 /dataLow:7000 /dataHigh:71ef /disablePolicyChecking+", "baseline")
            };

            //cross product
            return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectTimeoutIoVolumesBenchmarks()
        {
            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            //commening out > 50% of each set to get a primary run
            var dirs = new List<string>()  {
                    @"benchmarks"+s+"IoVolumes"+s+"func_0000000000003620"
                    ,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000038C0"
            };

            var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2f60 /funcGuardCheckIcallCfw:50d0 /funcMemset:3960 /funcMemcpy:3bb0 /funcMemcmp:3e80 /funcSGXMalloc:4fa0 /funcSGXFree:4fa6 /dataLow:7000 /dataHigh:71ef", "baseline")
            };

            //cross product
            return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectIoVolumesBenchmarks()
        {
          var bplFile = @"dll_func.bpl";
          var s = IsLinux() ? @"/" : @"\";

          //commening out > 50% of each set to get a primary run
          var dirs = new List<string>()  {
                    // @"benchmarks"+s+"IoVolumes"+s+"func_0000000000001000"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000010B0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000001120"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000011E0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000001210"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000001270"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000012D0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000001330"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000001390"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000001400"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000001540"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000001590"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000017F0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000001F60"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000025A0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000025B0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000025C0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002660"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002690"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002760"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002850"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002CF0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002D60"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002DD0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002DE0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002F30"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002F80"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000002FB0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000003010"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000003070"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000003200"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000003310"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000003370"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000003380"
                    @"benchmarks"+s+"IoVolumes"+s+"func_0000000000003620"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000003810"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000038B0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000038C0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000003B90"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000004950"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000004AD0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000004C40"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000050D0"
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000005150"
                    ////,@"benchmarks"+s+"IoVolumes"+s+"func_0000000000005160" //_guard_init_region should not be in U
                    //,@"benchmarks"+s+"IoVolumes"+s+"func_00000000000052D0"
            };

          var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2f60 /funcGuardCheckIcallCfw:50d0 /funcMemset:3960 /funcMemcpy:3bb0 /funcMemcmp:3e80 /funcSGXMalloc:4fa0 /funcSGXFree:4fa6 /dataLow:7000 /dataHigh:71ef", "baseline")
            };

          //cross product
          return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectSampleBenchmarks()
        {
            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            var dirs = new List<string>()  {
                 @"benchmarks"+s+"stackread"+s+"func_0000000000001000"
                ,@"benchmarks"+s+"stackread"+s+"func_0000000000001120"
                ,@"benchmarks"+s+"stackwrite"+s+"func_0000000000001000"
                ,@"benchmarks"+s+"stackwrite"+s+"func_0000000000001240"
                ,@"benchmarks"+s+"unknownaddrwrite"+s+"func_0000000000001000"
                ,@"benchmarks"+s+"unknownaddrwrite"+s+"func_0000000000001190"
                ,@"benchmarks"+s+"looparrayupdate"+s+"func_0000000000001000"
                ,@"benchmarks"+s+"looparrayupdate"+s+"func_0000000000001250"
                ,@"benchmarks"+s+"condjmp"+s+"func_0000000000001000"
                ,@"benchmarks"+s+"condjmp"+s+"func_0000000000001040"
                //,@"benchmarks"+s+"funcptr"+s+"func_0000000000001000" //fails in loop detector [boogie crash]
                //,@"benchmarks"+s+"funcptr"+s+"func_0000000000001040" //fails in loop detector [boogie crash]
                ,@"benchmarks"+s+"funcptr"+s+"func_0000000000001080"
                ,@"benchmarks"+s+"funcptr"+s+"func_00000000000010a0"
                ,@"benchmarks"+s+"funcptr"+s+"func_0000000000001140"
                ,@"benchmarks"+s+"writecallergrant"+s+"func_0000000000001000"
                ,@"benchmarks"+s+"writecallergrant"+s+"func_0000000000001090"
                ,@"benchmarks"+s+"writecallergrant"+s+"func_00000000000011f0"
                ,@"benchmarks"+s+"writecallerbitset"+s+"func_0000000000001000"
                ,@"benchmarks"+s+"writecallerbitset"+s+"func_0000000000001090"
                ,@"benchmarks"+s+"writecallerbitset"+s+"func_0000000000001240"
            };

            var options = new List<Tuple<string, string>>()
            {
                 Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2410 /funcGuardCheckIcallCfw:24b0 /funcMemset:2db0 /funcMemcpy:3000 /funcMemcmp:32d0 /funcSGXMalloc:43f0 /funcSGXFree:43f6 /dataLow:4000 /dataHigh:405f", "baseline")
            };

            //cross product
            List<Tuple<string, string, string, string>> tmp = new List<Tuple<string, string, string, string>>();
            tmp.AddRange(dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList());

            return tmp;
        }

        public static List<Tuple<string, string, string, string>> CollectTimeoutUserUsageBenchmarks()
        {

            var bplFile = @"dll_func.bpl";
            var s = IsLinux() ? @"/" : @"\";

            //commening out > 50% of each set to get a primary run
            var dirs = new List<string>()  {
              @"benchmarks"+s+"UserUsage"+s+"func_0000000000002A70"
              ,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002D10"
          };

            var options = new List<Tuple<string, string>>()
            {
                Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2410 /funcGuardCheckIcallCfw:4520 /funcMemset:2db0 /funcMemcpy:3000 /funcMemcmp:32d0 /funcSGXMalloc:43f0 /funcSGXFree:43f6 /dataLow:6000 /dataHigh:61bf", "baseline")
            };

            //cross product
            return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectUserUsageBenchmarks()
        {

          var bplFile = @"dll_func.bpl";
          var s = IsLinux() ? @"/" : @"\";

          //commening out > 50% of each set to get a primary run
          var dirs = new List<string>()  {
              // @"benchmarks"+s+"UserUsage"+s+"func_0000000000001650"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001780"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001A90"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002190"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002410"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002420"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002440"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002450"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000004570"
              ////,@"benchmarks"+s+"UserUsage"+s+"func_0000000000004590" //_guard_init_region should not be part of U
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000004660"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000004670"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001000"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001090"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001140"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000011C0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001280"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000012B0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001310"
              @"benchmarks"+s+"UserUsage"+s+"func_0000000000001370"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000013D0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001430"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001460"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000014B0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000016D0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000016E0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000016F0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000017A0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000019F0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001AC0"
              ////,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001B30" //fails in loop detector [Boogie crash]
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001D00"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001DF0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000001E90"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000021A0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002210"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002280"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002290"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000023E0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002430"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002460"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000024C0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002650"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002760"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000027C0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_00000000000027D0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002A70"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002C60"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002D00"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002D10"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000002FE0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000003DA0"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000003F20"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000004090"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000004520"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000004580"
              //,@"benchmarks"+s+"UserUsage"+s+"func_0000000000004720"
          };

          var options = new List<Tuple<string, string>>()
            {
                 //Tuple.Create(@"", "baseline")
                Tuple.Create(@" /confidentiality+ /instantiateQuantifiers+ /funcNew:2410 /funcGuardCheckIcallCfw:4520 /funcMemset:2db0 /funcMemcpy:3000 /funcMemcmp:32d0 /funcSGXMalloc:43f0 /funcSGXFree:43f6 /dataLow:6000 /dataHigh:61bf", "baseline")
            };

          //cross product
          return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        public static List<Tuple<string, string, string, string>> CollectCondJmpBenchmarks()
        {

          var bplFile = @"dll_func.bpl";
          var s = IsLinux() ? @"/" : @"\";

          //commening out > 50% of each set to get a primary run
          var dirs = new List<string>()  {
                 @"benchmarks"+s+"CondJmp"+s+"func_0000000000001000"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001040"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001090"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000010C0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000010D0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001260"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001280"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000012C0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001450"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001620"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001660"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001690"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000016D0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001710"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001750"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001BB0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001C00"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001DF0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001E90"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001EA0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000001F10"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002030"
                //,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002260"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000022B0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002350"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002380"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000023B0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002400"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002430"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002460"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002490"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000024B0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000024D0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002500"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002530"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002560"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002580"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002590"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000025A0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000025B0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000025C0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_00000000000025D0"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002700"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002800"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002920"
                ,@"benchmarks"+s+"CondJmp"+s+"func_0000000000002A30"
            };

          var options = new List<Tuple<string, string>>()
            {
                 //Tuple.Create(@"", "baseline")
                Tuple.Create(@" /instantiateQuantifiers+ /funcNew:2410 /funcGuardCheckIcallCfw:24b0 /funcMemset:2db0 /funcMemcpy:3000 /funcMemcmp:32d0 /funcSGXMalloc:43f0 /funcSGXFree:43f6 /dataLow:4000 /dataHigh:405f", "baseline")

            };

          //cross product
          return dirs.SelectMany(x => options, (x, y) => Tuple.Create(x, bplFile, y.Item1, y.Item2)).ToList();
        }

        internal static void CollectBenchmarks(String[] args, ref List<Tuple<string, string, string, string>> inputs)
        {
          if (args.Contains("condjmp")) { inputs.AddRange(Options.CollectCondJmpBenchmarks()); }
          if (args.Contains("aggregate")) {
              if (args.Contains("/option:timeout")) { inputs.AddRange(Options.CollectTimeoutAggregateBenchmarks()); }
              else { inputs.AddRange(Options.CollectAggregateBenchmarks()); }
          }
          if (args.Contains("iovolumes"))
          {
              if (args.Contains("/option:timeout")) { inputs.AddRange(Options.CollectTimeoutIoVolumesBenchmarks()); }
              else { inputs.AddRange(Options.CollectIoVolumesBenchmarks()); }
          }
          if (args.Contains("userusage"))
          {
              if (args.Contains("/option:timeout")) { inputs.AddRange(Options.CollectTimeoutUserUsageBenchmarks()); }
              else { inputs.AddRange(Options.CollectUserUsageBenchmarks()); }
          }
          if (args.Contains("sample")) { inputs.AddRange(Options.CollectSampleBenchmarks()); }
          if (args.Contains("bzip2"))
          {
              if (args.Contains("/option:timeout")) { inputs.AddRange(Options.CollectTimeoutBzip2Benchmarks()); }
              else { inputs.AddRange(Options.CollectBzip2Benchmarks()); }
          }
          if (args.Contains("astar"))
          {
              if (args.Contains("/option:timeout")) { inputs.AddRange(Options.CollectTimeoutAStarBenchmarks()); }
              else { inputs.AddRange(Options.CollectAStarBenchmarks()); }
          }
          if (args.Contains("lbm"))
          {
              if (args.Contains("/option:timeout")) { inputs.AddRange(Options.CollectTimeoutLbmBenchmarks()); }
              else { inputs.AddRange(Options.CollectLbmBenchmarks()); }
          }
        }
    }
}
