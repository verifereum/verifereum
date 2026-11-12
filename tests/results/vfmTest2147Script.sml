Theory vfmTest2147[no_sig_docs]
Ancestors vfmTestDefs2147
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2147_0.nsv", "result2147_1.nsv", "result2147_2.nsv", "result2147_3.nsv", "result2147_4.nsv", "result2147_5.nsv", "result2147_6.nsv", "result2147_7.nsv", "result2147_8.nsv", "result2147_9.nsv", "result2147_10.nsv", "result2147_11.nsv", "result2147_12.nsv", "result2147_13.nsv", "result2147_14.nsv", "result2147_15.nsv", "result2147_16.nsv", "result2147_17.nsv", "result2147_18.nsv", "result2147_19.nsv", "result2147_20.nsv", "result2147_21.nsv", "result2147_22.nsv", "result2147_23.nsv", "result2147_24.nsv", "result2147_25.nsv", "result2147_26.nsv"];
val thyn = "vfmTestDefs2147";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
