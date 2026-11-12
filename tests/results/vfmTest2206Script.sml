Theory vfmTest2206[no_sig_docs]
Ancestors vfmTestDefs2206
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2206_0.nsv", "result2206_1.nsv", "result2206_2.nsv", "result2206_3.nsv", "result2206_4.nsv", "result2206_5.nsv", "result2206_6.nsv", "result2206_7.nsv", "result2206_8.nsv", "result2206_9.nsv", "result2206_10.nsv", "result2206_11.nsv", "result2206_12.nsv", "result2206_13.nsv", "result2206_14.nsv", "result2206_15.nsv", "result2206_16.nsv", "result2206_17.nsv", "result2206_18.nsv", "result2206_19.nsv", "result2206_20.nsv", "result2206_21.nsv", "result2206_22.nsv", "result2206_23.nsv", "result2206_24.nsv", "result2206_25.nsv", "result2206_26.nsv", "result2206_27.nsv", "result2206_28.nsv", "result2206_29.nsv", "result2206_30.nsv", "result2206_31.nsv", "result2206_32.nsv", "result2206_33.nsv", "result2206_34.nsv", "result2206_35.nsv"];
val thyn = "vfmTestDefs2206";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
