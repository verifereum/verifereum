Theory vfmTest0788[no_sig_docs]
Ancestors vfmTestDefs0788
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0788_0.nsv", "result0788_1.nsv", "result0788_2.nsv"];
val thyn = "vfmTestDefs0788";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
