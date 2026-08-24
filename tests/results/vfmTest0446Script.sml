Theory vfmTest0446[no_sig_docs]
Ancestors vfmTestDefs0446
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0446_0.nsv", "result0446_1.nsv", "result0446_2.nsv"];
val thyn = "vfmTestDefs0446";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
