Theory vfmTest2575[no_sig_docs]
Ancestors vfmTestDefs2575
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2575_0.nsv"];
val thyn = "vfmTestDefs2575";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
