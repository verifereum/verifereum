Theory vfmTest1655[no_sig_docs]
Ancestors vfmTestDefs1655
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1655_0.nsv", "result1655_1.nsv", "result1655_2.nsv", "result1655_3.nsv", "result1655_4.nsv", "result1655_5.nsv", "result1655_6.nsv", "result1655_7.nsv", "result1655_8.nsv", "result1655_9.nsv", "result1655_10.nsv", "result1655_11.nsv", "result1655_12.nsv", "result1655_13.nsv", "result1655_14.nsv", "result1655_15.nsv", "result1655_16.nsv", "result1655_17.nsv", "result1655_18.nsv", "result1655_19.nsv"];
val thyn = "vfmTestDefs1655";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
