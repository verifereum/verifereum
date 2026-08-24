Theory vfmTest0675[no_sig_docs]
Ancestors vfmTestDefs0675
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0675_0.nsv"];
val thyn = "vfmTestDefs0675";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
