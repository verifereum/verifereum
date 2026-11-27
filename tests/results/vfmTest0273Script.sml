Theory vfmTest0273[no_sig_docs]
Ancestors vfmTestDefs0273
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0273_0.nsv", "result0273_1.nsv", "result0273_2.nsv", "result0273_3.nsv", "result0273_4.nsv", "result0273_5.nsv", "result0273_6.nsv", "result0273_7.nsv", "result0273_8.nsv", "result0273_9.nsv", "result0273_10.nsv", "result0273_11.nsv", "result0273_12.nsv", "result0273_13.nsv", "result0273_14.nsv"];
val thyn = "vfmTestDefs0273";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
