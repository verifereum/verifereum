Theory vfmTest0705[no_sig_docs]
Ancestors vfmTestDefs0705
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0705_0.nsv", "result0705_1.nsv", "result0705_2.nsv", "result0705_3.nsv", "result0705_4.nsv", "result0705_5.nsv", "result0705_6.nsv", "result0705_7.nsv", "result0705_8.nsv", "result0705_9.nsv", "result0705_10.nsv", "result0705_11.nsv", "result0705_12.nsv", "result0705_13.nsv", "result0705_14.nsv", "result0705_15.nsv"];
val thyn = "vfmTestDefs0705";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
