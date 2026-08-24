Theory vfmTest0223[no_sig_docs]
Ancestors vfmTestDefs0223
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0223_0.nsv", "result0223_1.nsv", "result0223_2.nsv", "result0223_3.nsv"];
val thyn = "vfmTestDefs0223";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
