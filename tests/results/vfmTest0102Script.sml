Theory vfmTest0102[no_sig_docs]
Ancestors vfmTestDefs0102
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0102_0.nsv", "result0102_1.nsv", "result0102_2.nsv", "result0102_3.nsv", "result0102_4.nsv", "result0102_5.nsv", "result0102_6.nsv", "result0102_7.nsv", "result0102_8.nsv", "result0102_9.nsv", "result0102_10.nsv", "result0102_11.nsv", "result0102_12.nsv", "result0102_13.nsv", "result0102_14.nsv", "result0102_15.nsv", "result0102_16.nsv", "result0102_17.nsv", "result0102_18.nsv", "result0102_19.nsv"];
val thyn = "vfmTestDefs0102";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
