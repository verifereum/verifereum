Theory vfmTest2302[no_sig_docs]
Ancestors vfmTestDefs2302
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2302_0.nsv", "result2302_1.nsv", "result2302_2.nsv", "result2302_3.nsv", "result2302_4.nsv", "result2302_5.nsv", "result2302_6.nsv", "result2302_7.nsv", "result2302_8.nsv", "result2302_9.nsv", "result2302_10.nsv", "result2302_11.nsv", "result2302_12.nsv", "result2302_13.nsv", "result2302_14.nsv", "result2302_15.nsv", "result2302_16.nsv", "result2302_17.nsv", "result2302_18.nsv", "result2302_19.nsv", "result2302_20.nsv", "result2302_21.nsv", "result2302_22.nsv", "result2302_23.nsv", "result2302_24.nsv", "result2302_25.nsv", "result2302_26.nsv", "result2302_27.nsv", "result2302_28.nsv", "result2302_29.nsv", "result2302_30.nsv", "result2302_31.nsv", "result2302_32.nsv", "result2302_33.nsv", "result2302_34.nsv"];
val thyn = "vfmTestDefs2302";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
