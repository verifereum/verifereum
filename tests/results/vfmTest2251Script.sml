Theory vfmTest2251[no_sig_docs]
Ancestors vfmTestDefs2251
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2251_0.nsv", "result2251_1.nsv"];
val thyn = "vfmTestDefs2251";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
