Theory vfmTest2383[no_sig_docs]
Ancestors vfmTestDefs2383
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2383_0.nsv", "result2383_1.nsv", "result2383_2.nsv", "result2383_3.nsv", "result2383_4.nsv", "result2383_5.nsv", "result2383_6.nsv", "result2383_7.nsv", "result2383_8.nsv", "result2383_9.nsv", "result2383_10.nsv", "result2383_11.nsv", "result2383_12.nsv", "result2383_13.nsv", "result2383_14.nsv", "result2383_15.nsv", "result2383_16.nsv", "result2383_17.nsv", "result2383_18.nsv", "result2383_19.nsv"];
val thyn = "vfmTestDefs2383";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
