Theory vfmTest2339[no_sig_docs]
Ancestors vfmTestDefs2339
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2339_0.nsv", "result2339_1.nsv", "result2339_2.nsv", "result2339_3.nsv", "result2339_4.nsv", "result2339_5.nsv", "result2339_6.nsv", "result2339_7.nsv", "result2339_8.nsv", "result2339_9.nsv", "result2339_10.nsv", "result2339_11.nsv", "result2339_12.nsv", "result2339_13.nsv", "result2339_14.nsv", "result2339_15.nsv", "result2339_16.nsv", "result2339_17.nsv", "result2339_18.nsv", "result2339_19.nsv", "result2339_20.nsv", "result2339_21.nsv", "result2339_22.nsv", "result2339_23.nsv"];
val thyn = "vfmTestDefs2339";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
