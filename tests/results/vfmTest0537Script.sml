Theory vfmTest0537[no_sig_docs]
Ancestors vfmTestDefs0537
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0537_0.nsv"];
val thyn = "vfmTestDefs0537";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
