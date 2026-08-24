Theory vfmTest0921[no_sig_docs]
Ancestors vfmTestDefs0921
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0921_0.nsv"];
val thyn = "vfmTestDefs0921";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
