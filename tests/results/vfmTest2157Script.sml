Theory vfmTest2157[no_sig_docs]
Ancestors vfmTestDefs2157
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2157_0.nsv", "result2157_1.nsv", "result2157_2.nsv", "result2157_3.nsv", "result2157_4.nsv", "result2157_5.nsv", "result2157_6.nsv", "result2157_7.nsv", "result2157_8.nsv", "result2157_9.nsv", "result2157_10.nsv", "result2157_11.nsv", "result2157_12.nsv", "result2157_13.nsv", "result2157_14.nsv", "result2157_15.nsv", "result2157_16.nsv", "result2157_17.nsv", "result2157_18.nsv", "result2157_19.nsv", "result2157_20.nsv", "result2157_21.nsv", "result2157_22.nsv", "result2157_23.nsv", "result2157_24.nsv", "result2157_25.nsv", "result2157_26.nsv", "result2157_27.nsv", "result2157_28.nsv", "result2157_29.nsv", "result2157_30.nsv", "result2157_31.nsv", "result2157_32.nsv", "result2157_33.nsv"];
val thyn = "vfmTestDefs2157";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
