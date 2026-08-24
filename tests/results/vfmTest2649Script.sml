Theory vfmTest2649[no_sig_docs]
Ancestors vfmTestDefs2649
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2649_0.nsv", "result2649_1.nsv", "result2649_2.nsv", "result2649_3.nsv"];
val thyn = "vfmTestDefs2649";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
