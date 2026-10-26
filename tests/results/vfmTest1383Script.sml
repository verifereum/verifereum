Theory vfmTest1383[no_sig_docs]
Ancestors vfmTestDefs1383
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1383_0.nsv", "result1383_1.nsv", "result1383_2.nsv", "result1383_3.nsv", "result1383_4.nsv", "result1383_5.nsv", "result1383_6.nsv", "result1383_7.nsv", "result1383_8.nsv", "result1383_9.nsv", "result1383_10.nsv", "result1383_11.nsv", "result1383_12.nsv", "result1383_13.nsv", "result1383_14.nsv", "result1383_15.nsv", "result1383_16.nsv", "result1383_17.nsv", "result1383_18.nsv", "result1383_19.nsv", "result1383_20.nsv", "result1383_21.nsv", "result1383_22.nsv", "result1383_23.nsv", "result1383_24.nsv", "result1383_25.nsv", "result1383_26.nsv", "result1383_27.nsv", "result1383_28.nsv", "result1383_29.nsv", "result1383_30.nsv", "result1383_31.nsv"];
val thyn = "vfmTestDefs1383";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
