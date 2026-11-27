Theory vfmTest2295[no_sig_docs]
Ancestors vfmTestDefs2295
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2295_0.nsv", "result2295_1.nsv", "result2295_2.nsv", "result2295_3.nsv", "result2295_4.nsv", "result2295_5.nsv", "result2295_6.nsv", "result2295_7.nsv", "result2295_8.nsv", "result2295_9.nsv", "result2295_10.nsv", "result2295_11.nsv", "result2295_12.nsv", "result2295_13.nsv", "result2295_14.nsv", "result2295_15.nsv", "result2295_16.nsv", "result2295_17.nsv", "result2295_18.nsv", "result2295_19.nsv", "result2295_20.nsv", "result2295_21.nsv", "result2295_22.nsv"];
val thyn = "vfmTestDefs2295";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
