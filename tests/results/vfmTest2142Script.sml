Theory vfmTest2142[no_sig_docs]
Ancestors vfmTestDefs2142
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2142_0.nsv", "result2142_1.nsv", "result2142_2.nsv", "result2142_3.nsv", "result2142_4.nsv", "result2142_5.nsv", "result2142_6.nsv", "result2142_7.nsv", "result2142_8.nsv", "result2142_9.nsv", "result2142_10.nsv", "result2142_11.nsv", "result2142_12.nsv", "result2142_13.nsv", "result2142_14.nsv", "result2142_15.nsv", "result2142_16.nsv", "result2142_17.nsv", "result2142_18.nsv", "result2142_19.nsv", "result2142_20.nsv", "result2142_21.nsv", "result2142_22.nsv", "result2142_23.nsv", "result2142_24.nsv", "result2142_25.nsv", "result2142_26.nsv", "result2142_27.nsv", "result2142_28.nsv", "result2142_29.nsv", "result2142_30.nsv", "result2142_31.nsv", "result2142_32.nsv", "result2142_33.nsv"];
val thyn = "vfmTestDefs2142";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
