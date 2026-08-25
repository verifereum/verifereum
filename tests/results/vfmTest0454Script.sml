Theory vfmTest0454[no_sig_docs]
Ancestors vfmTestDefs0454
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0454_0.nsv", "result0454_1.nsv", "result0454_2.nsv", "result0454_3.nsv", "result0454_4.nsv", "result0454_5.nsv"];
val thyn = "vfmTestDefs0454";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
