Theory vfmTest0176[no_sig_docs]
Ancestors vfmTestDefs0176
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0176_0.nsv", "result0176_1.nsv", "result0176_2.nsv", "result0176_3.nsv", "result0176_4.nsv", "result0176_5.nsv", "result0176_6.nsv", "result0176_7.nsv", "result0176_8.nsv"];
val thyn = "vfmTestDefs0176";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
