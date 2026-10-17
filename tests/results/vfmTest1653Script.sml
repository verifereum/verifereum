Theory vfmTest1653[no_sig_docs]
Ancestors vfmTestDefs1653
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1653_0.nsv", "result1653_1.nsv", "result1653_2.nsv", "result1653_3.nsv", "result1653_4.nsv", "result1653_5.nsv", "result1653_6.nsv", "result1653_7.nsv", "result1653_8.nsv", "result1653_9.nsv", "result1653_10.nsv", "result1653_11.nsv", "result1653_12.nsv", "result1653_13.nsv", "result1653_14.nsv", "result1653_15.nsv", "result1653_16.nsv", "result1653_17.nsv", "result1653_18.nsv", "result1653_19.nsv"];
val thyn = "vfmTestDefs1653";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
