Theory vfmTest1982[no_sig_docs]
Ancestors vfmTestDefs1982
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1982_0.nsv", "result1982_1.nsv", "result1982_2.nsv", "result1982_3.nsv", "result1982_4.nsv", "result1982_5.nsv", "result1982_6.nsv", "result1982_7.nsv", "result1982_8.nsv", "result1982_9.nsv", "result1982_10.nsv", "result1982_11.nsv", "result1982_12.nsv", "result1982_13.nsv", "result1982_14.nsv", "result1982_15.nsv", "result1982_16.nsv", "result1982_17.nsv", "result1982_18.nsv", "result1982_19.nsv"];
val thyn = "vfmTestDefs1982";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
