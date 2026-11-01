Theory vfmTest0633[no_sig_docs]
Ancestors vfmTestDefs0633
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0633_0.nsv", "result0633_1.nsv", "result0633_2.nsv", "result0633_3.nsv", "result0633_4.nsv", "result0633_5.nsv", "result0633_6.nsv", "result0633_7.nsv", "result0633_8.nsv", "result0633_9.nsv"];
val thyn = "vfmTestDefs0633";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
