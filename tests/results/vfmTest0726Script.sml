Theory vfmTest0726[no_sig_docs]
Ancestors vfmTestDefs0726
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0726_0.nsv"];
val thyn = "vfmTestDefs0726";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
