Theory vfmTest0205[no_sig_docs]
Ancestors vfmTestDefs0205
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0205_0.nsv", "result0205_1.nsv", "result0205_2.nsv", "result0205_3.nsv", "result0205_4.nsv", "result0205_5.nsv", "result0205_6.nsv", "result0205_7.nsv", "result0205_8.nsv", "result0205_9.nsv", "result0205_10.nsv", "result0205_11.nsv", "result0205_12.nsv", "result0205_13.nsv", "result0205_14.nsv", "result0205_15.nsv", "result0205_16.nsv", "result0205_17.nsv", "result0205_18.nsv", "result0205_19.nsv", "result0205_20.nsv"];
val thyn = "vfmTestDefs0205";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
