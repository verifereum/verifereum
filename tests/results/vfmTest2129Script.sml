Theory vfmTest2129[no_sig_docs]
Ancestors vfmTestDefs2129
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2129_0.nsv", "result2129_1.nsv", "result2129_2.nsv", "result2129_3.nsv", "result2129_4.nsv", "result2129_5.nsv", "result2129_6.nsv", "result2129_7.nsv", "result2129_8.nsv", "result2129_9.nsv", "result2129_10.nsv", "result2129_11.nsv", "result2129_12.nsv", "result2129_13.nsv", "result2129_14.nsv", "result2129_15.nsv", "result2129_16.nsv", "result2129_17.nsv", "result2129_18.nsv", "result2129_19.nsv", "result2129_20.nsv", "result2129_21.nsv", "result2129_22.nsv", "result2129_23.nsv", "result2129_24.nsv", "result2129_25.nsv", "result2129_26.nsv", "result2129_27.nsv", "result2129_28.nsv", "result2129_29.nsv", "result2129_30.nsv", "result2129_31.nsv", "result2129_32.nsv", "result2129_33.nsv", "result2129_34.nsv", "result2129_35.nsv"];
val thyn = "vfmTestDefs2129";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
