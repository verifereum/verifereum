Theory vfmTest2338[no_sig_docs]
Ancestors vfmTestDefs2338
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2338_0.nsv", "result2338_1.nsv", "result2338_2.nsv", "result2338_3.nsv", "result2338_4.nsv", "result2338_5.nsv", "result2338_6.nsv", "result2338_7.nsv", "result2338_8.nsv", "result2338_9.nsv", "result2338_10.nsv", "result2338_11.nsv", "result2338_12.nsv", "result2338_13.nsv", "result2338_14.nsv", "result2338_15.nsv", "result2338_16.nsv", "result2338_17.nsv", "result2338_18.nsv", "result2338_19.nsv", "result2338_20.nsv", "result2338_21.nsv", "result2338_22.nsv", "result2338_23.nsv", "result2338_24.nsv", "result2338_25.nsv", "result2338_26.nsv", "result2338_27.nsv", "result2338_28.nsv", "result2338_29.nsv", "result2338_30.nsv", "result2338_31.nsv", "result2338_32.nsv", "result2338_33.nsv", "result2338_34.nsv", "result2338_35.nsv"];
val thyn = "vfmTestDefs2338";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
