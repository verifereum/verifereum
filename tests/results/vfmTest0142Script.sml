Theory vfmTest0142[no_sig_docs]
Ancestors vfmTestDefs0142
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0142_0.nsv", "result0142_1.nsv", "result0142_2.nsv", "result0142_3.nsv", "result0142_4.nsv", "result0142_5.nsv", "result0142_6.nsv", "result0142_7.nsv", "result0142_8.nsv", "result0142_9.nsv", "result0142_10.nsv", "result0142_11.nsv", "result0142_12.nsv", "result0142_13.nsv", "result0142_14.nsv", "result0142_15.nsv"];
val thyn = "vfmTestDefs0142";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
