Theory vfmTest1660[no_sig_docs]
Ancestors vfmTestDefs1660
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1660_0.nsv", "result1660_1.nsv", "result1660_2.nsv", "result1660_3.nsv", "result1660_4.nsv", "result1660_5.nsv", "result1660_6.nsv", "result1660_7.nsv", "result1660_8.nsv", "result1660_9.nsv", "result1660_10.nsv", "result1660_11.nsv", "result1660_12.nsv", "result1660_13.nsv", "result1660_14.nsv", "result1660_15.nsv", "result1660_16.nsv", "result1660_17.nsv", "result1660_18.nsv", "result1660_19.nsv"];
val thyn = "vfmTestDefs1660";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
