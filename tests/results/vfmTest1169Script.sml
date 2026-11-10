Theory vfmTest1169[no_sig_docs]
Ancestors vfmTestDefs1169
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1169_0.nsv", "result1169_1.nsv", "result1169_2.nsv", "result1169_3.nsv", "result1169_4.nsv", "result1169_5.nsv", "result1169_6.nsv", "result1169_7.nsv", "result1169_8.nsv", "result1169_9.nsv", "result1169_10.nsv", "result1169_11.nsv", "result1169_12.nsv", "result1169_13.nsv", "result1169_14.nsv", "result1169_15.nsv", "result1169_16.nsv", "result1169_17.nsv", "result1169_18.nsv", "result1169_19.nsv", "result1169_20.nsv"];
val thyn = "vfmTestDefs1169";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
