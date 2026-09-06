Theory vfmTest1676[no_sig_docs]
Ancestors vfmTestDefs1676
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1676_0.nsv", "result1676_1.nsv", "result1676_2.nsv", "result1676_3.nsv", "result1676_4.nsv", "result1676_5.nsv", "result1676_6.nsv", "result1676_7.nsv", "result1676_8.nsv", "result1676_9.nsv", "result1676_10.nsv", "result1676_11.nsv", "result1676_12.nsv", "result1676_13.nsv", "result1676_14.nsv", "result1676_15.nsv", "result1676_16.nsv", "result1676_17.nsv", "result1676_18.nsv", "result1676_19.nsv"];
val thyn = "vfmTestDefs1676";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
