Theory vfmTest2457[no_sig_docs]
Ancestors vfmTestDefs2457
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2457_0.nsv", "result2457_1.nsv", "result2457_2.nsv", "result2457_3.nsv", "result2457_4.nsv", "result2457_5.nsv", "result2457_6.nsv", "result2457_7.nsv", "result2457_8.nsv", "result2457_9.nsv", "result2457_10.nsv", "result2457_11.nsv", "result2457_12.nsv", "result2457_13.nsv", "result2457_14.nsv", "result2457_15.nsv", "result2457_16.nsv", "result2457_17.nsv", "result2457_18.nsv", "result2457_19.nsv", "result2457_20.nsv", "result2457_21.nsv", "result2457_22.nsv", "result2457_23.nsv", "result2457_24.nsv", "result2457_25.nsv", "result2457_26.nsv", "result2457_27.nsv", "result2457_28.nsv", "result2457_29.nsv", "result2457_30.nsv", "result2457_31.nsv", "result2457_32.nsv", "result2457_33.nsv", "result2457_34.nsv", "result2457_35.nsv"];
val thyn = "vfmTestDefs2457";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
