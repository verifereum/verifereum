Theory vfmTest1670[no_sig_docs]
Ancestors vfmTestDefs1670
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1670_0.nsv", "result1670_1.nsv", "result1670_2.nsv", "result1670_3.nsv", "result1670_4.nsv", "result1670_5.nsv", "result1670_6.nsv", "result1670_7.nsv", "result1670_8.nsv", "result1670_9.nsv", "result1670_10.nsv", "result1670_11.nsv", "result1670_12.nsv", "result1670_13.nsv", "result1670_14.nsv", "result1670_15.nsv", "result1670_16.nsv", "result1670_17.nsv", "result1670_18.nsv", "result1670_19.nsv"];
val thyn = "vfmTestDefs1670";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
