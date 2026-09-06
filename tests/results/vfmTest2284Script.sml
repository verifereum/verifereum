Theory vfmTest2284[no_sig_docs]
Ancestors vfmTestDefs2284
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2284_0.nsv", "result2284_1.nsv", "result2284_2.nsv", "result2284_3.nsv", "result2284_4.nsv", "result2284_5.nsv", "result2284_6.nsv", "result2284_7.nsv", "result2284_8.nsv", "result2284_9.nsv", "result2284_10.nsv", "result2284_11.nsv", "result2284_12.nsv", "result2284_13.nsv", "result2284_14.nsv", "result2284_15.nsv", "result2284_16.nsv", "result2284_17.nsv", "result2284_18.nsv", "result2284_19.nsv", "result2284_20.nsv", "result2284_21.nsv", "result2284_22.nsv", "result2284_23.nsv", "result2284_24.nsv", "result2284_25.nsv", "result2284_26.nsv", "result2284_27.nsv", "result2284_28.nsv", "result2284_29.nsv", "result2284_30.nsv", "result2284_31.nsv", "result2284_32.nsv", "result2284_33.nsv", "result2284_34.nsv", "result2284_35.nsv"];
val thyn = "vfmTestDefs2284";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
