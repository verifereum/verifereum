Theory vfmTest2402[no_sig_docs]
Ancestors vfmTestDefs2402
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2402_0.nsv", "result2402_1.nsv", "result2402_2.nsv", "result2402_3.nsv", "result2402_4.nsv", "result2402_5.nsv", "result2402_6.nsv", "result2402_7.nsv", "result2402_8.nsv"];
val thyn = "vfmTestDefs2402";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
