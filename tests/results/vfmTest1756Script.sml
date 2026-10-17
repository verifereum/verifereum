Theory vfmTest1756[no_sig_docs]
Ancestors vfmTestDefs1756
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1756_0.nsv", "result1756_1.nsv", "result1756_2.nsv", "result1756_3.nsv", "result1756_4.nsv", "result1756_5.nsv", "result1756_6.nsv", "result1756_7.nsv", "result1756_8.nsv", "result1756_9.nsv", "result1756_10.nsv", "result1756_11.nsv", "result1756_12.nsv", "result1756_13.nsv", "result1756_14.nsv", "result1756_15.nsv", "result1756_16.nsv", "result1756_17.nsv", "result1756_18.nsv", "result1756_19.nsv", "result1756_20.nsv", "result1756_21.nsv", "result1756_22.nsv", "result1756_23.nsv", "result1756_24.nsv", "result1756_25.nsv", "result1756_26.nsv", "result1756_27.nsv", "result1756_28.nsv", "result1756_29.nsv", "result1756_30.nsv", "result1756_31.nsv"];
val thyn = "vfmTestDefs1756";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
