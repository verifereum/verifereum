Theory vfmTest1659[no_sig_docs]
Ancestors vfmTestDefs1659
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1659_0.nsv", "result1659_1.nsv", "result1659_2.nsv", "result1659_3.nsv", "result1659_4.nsv", "result1659_5.nsv", "result1659_6.nsv", "result1659_7.nsv", "result1659_8.nsv", "result1659_9.nsv", "result1659_10.nsv", "result1659_11.nsv", "result1659_12.nsv", "result1659_13.nsv", "result1659_14.nsv", "result1659_15.nsv", "result1659_16.nsv", "result1659_17.nsv", "result1659_18.nsv", "result1659_19.nsv"];
val thyn = "vfmTestDefs1659";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
