Theory vfmTest2080[no_sig_docs]
Ancestors vfmTestDefs2080
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2080_0.nsv", "result2080_1.nsv", "result2080_2.nsv", "result2080_3.nsv", "result2080_4.nsv", "result2080_5.nsv", "result2080_6.nsv", "result2080_7.nsv", "result2080_8.nsv", "result2080_9.nsv", "result2080_10.nsv", "result2080_11.nsv", "result2080_12.nsv", "result2080_13.nsv", "result2080_14.nsv", "result2080_15.nsv", "result2080_16.nsv", "result2080_17.nsv", "result2080_18.nsv", "result2080_19.nsv", "result2080_20.nsv", "result2080_21.nsv", "result2080_22.nsv", "result2080_23.nsv", "result2080_24.nsv", "result2080_25.nsv", "result2080_26.nsv", "result2080_27.nsv", "result2080_28.nsv", "result2080_29.nsv", "result2080_30.nsv"];
val thyn = "vfmTestDefs2080";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
