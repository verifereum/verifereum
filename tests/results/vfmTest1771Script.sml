Theory vfmTest1771[no_sig_docs]
Ancestors vfmTestDefs1771
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1771_0.nsv", "result1771_1.nsv", "result1771_2.nsv", "result1771_3.nsv", "result1771_4.nsv", "result1771_5.nsv", "result1771_6.nsv", "result1771_7.nsv", "result1771_8.nsv", "result1771_9.nsv", "result1771_10.nsv", "result1771_11.nsv", "result1771_12.nsv", "result1771_13.nsv", "result1771_14.nsv", "result1771_15.nsv", "result1771_16.nsv", "result1771_17.nsv", "result1771_18.nsv", "result1771_19.nsv", "result1771_20.nsv", "result1771_21.nsv", "result1771_22.nsv", "result1771_23.nsv", "result1771_24.nsv", "result1771_25.nsv", "result1771_26.nsv", "result1771_27.nsv", "result1771_28.nsv", "result1771_29.nsv", "result1771_30.nsv", "result1771_31.nsv"];
val thyn = "vfmTestDefs1771";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
