Theory vfmTest2438[no_sig_docs]
Ancestors vfmTestDefs2438
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2438_0.nsv", "result2438_1.nsv", "result2438_2.nsv", "result2438_3.nsv"];
val thyn = "vfmTestDefs2438";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
