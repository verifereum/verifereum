Theory vfmTest2477[no_sig_docs]
Ancestors vfmTestDefs2477
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2477_0.nsv", "result2477_1.nsv", "result2477_2.nsv", "result2477_3.nsv", "result2477_4.nsv", "result2477_5.nsv", "result2477_6.nsv", "result2477_7.nsv", "result2477_8.nsv", "result2477_9.nsv", "result2477_10.nsv", "result2477_11.nsv", "result2477_12.nsv", "result2477_13.nsv", "result2477_14.nsv", "result2477_15.nsv", "result2477_16.nsv", "result2477_17.nsv", "result2477_18.nsv", "result2477_19.nsv", "result2477_20.nsv", "result2477_21.nsv", "result2477_22.nsv", "result2477_23.nsv", "result2477_24.nsv", "result2477_25.nsv", "result2477_26.nsv", "result2477_27.nsv", "result2477_28.nsv", "result2477_29.nsv"];
val thyn = "vfmTestDefs2477";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
