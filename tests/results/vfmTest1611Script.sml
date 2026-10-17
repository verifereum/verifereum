Theory vfmTest1611[no_sig_docs]
Ancestors vfmTestDefs1611
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1611_0.nsv", "result1611_1.nsv", "result1611_2.nsv", "result1611_3.nsv", "result1611_4.nsv", "result1611_5.nsv", "result1611_6.nsv", "result1611_7.nsv", "result1611_8.nsv", "result1611_9.nsv", "result1611_10.nsv", "result1611_11.nsv", "result1611_12.nsv", "result1611_13.nsv", "result1611_14.nsv", "result1611_15.nsv", "result1611_16.nsv", "result1611_17.nsv", "result1611_18.nsv", "result1611_19.nsv", "result1611_20.nsv", "result1611_21.nsv", "result1611_22.nsv", "result1611_23.nsv"];
val thyn = "vfmTestDefs1611";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
