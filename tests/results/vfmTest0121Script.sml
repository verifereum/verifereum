Theory vfmTest0121[no_sig_docs]
Ancestors vfmTestDefs0121
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0121_0.nsv", "result0121_1.nsv"];
val thyn = "vfmTestDefs0121";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
