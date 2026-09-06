Theory vfmTest1692[no_sig_docs]
Ancestors vfmTestDefs1692
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1692_0.nsv", "result1692_1.nsv", "result1692_2.nsv", "result1692_3.nsv", "result1692_4.nsv", "result1692_5.nsv", "result1692_6.nsv", "result1692_7.nsv", "result1692_8.nsv", "result1692_9.nsv", "result1692_10.nsv", "result1692_11.nsv", "result1692_12.nsv", "result1692_13.nsv", "result1692_14.nsv", "result1692_15.nsv", "result1692_16.nsv", "result1692_17.nsv", "result1692_18.nsv", "result1692_19.nsv"];
val thyn = "vfmTestDefs1692";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
