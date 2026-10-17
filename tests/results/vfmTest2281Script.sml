Theory vfmTest2281[no_sig_docs]
Ancestors vfmTestDefs2281
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2281_0.nsv", "result2281_1.nsv", "result2281_2.nsv", "result2281_3.nsv", "result2281_4.nsv", "result2281_5.nsv", "result2281_6.nsv", "result2281_7.nsv", "result2281_8.nsv", "result2281_9.nsv", "result2281_10.nsv", "result2281_11.nsv", "result2281_12.nsv", "result2281_13.nsv", "result2281_14.nsv", "result2281_15.nsv", "result2281_16.nsv", "result2281_17.nsv", "result2281_18.nsv", "result2281_19.nsv", "result2281_20.nsv", "result2281_21.nsv", "result2281_22.nsv", "result2281_23.nsv", "result2281_24.nsv", "result2281_25.nsv", "result2281_26.nsv"];
val thyn = "vfmTestDefs2281";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
