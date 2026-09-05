Theory vfmTest1683[no_sig_docs]
Ancestors vfmTestDefs1683
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1683_0.nsv", "result1683_1.nsv", "result1683_2.nsv", "result1683_3.nsv", "result1683_4.nsv", "result1683_5.nsv", "result1683_6.nsv", "result1683_7.nsv", "result1683_8.nsv", "result1683_9.nsv", "result1683_10.nsv", "result1683_11.nsv", "result1683_12.nsv", "result1683_13.nsv", "result1683_14.nsv", "result1683_15.nsv", "result1683_16.nsv", "result1683_17.nsv", "result1683_18.nsv", "result1683_19.nsv"];
val thyn = "vfmTestDefs1683";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
