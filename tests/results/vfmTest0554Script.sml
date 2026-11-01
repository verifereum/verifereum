Theory vfmTest0554[no_sig_docs]
Ancestors vfmTestDefs0554
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0554_0.nsv", "result0554_1.nsv", "result0554_2.nsv", "result0554_3.nsv", "result0554_4.nsv", "result0554_5.nsv"];
val thyn = "vfmTestDefs0554";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
