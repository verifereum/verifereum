Theory vfmTest2570[no_sig_docs]
Ancestors vfmTestDefs2570
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2570_0.nsv"];
val thyn = "vfmTestDefs2570";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
