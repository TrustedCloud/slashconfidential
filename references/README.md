1. `git clone` https://github.com/boogie-org/boogie
2. `msbuild boogie\Source\Boogie.sln`, or alternatively build using Visual Studio
3. execute `copy_boogie_libs.bat boogie\Binaries`
4. download z3 version 4.4.1 (https://github.com/Z3Prover/z3/releases/tag/z3-4.4.1)
5. `msbuild ..\SlashConfidential.sln` (so that the bin\Debug folder is generated for the next step)
6. `cp z3.exe ..\CfiVerifier\bin\Debug`
