Theory vfmTest1891[no_sig_docs]
Ancestors vfmTestDefs1891
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1891_0.nsv", "result1891_1.nsv"];
val thyn = "vfmTestDefs1891";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
