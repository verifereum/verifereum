Theory vfmTest2693[no_sig_docs]
Ancestors vfmTestDefs2693
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2693_0.nsv", "result2693_1.nsv", "result2693_2.nsv", "result2693_3.nsv", "result2693_4.nsv", "result2693_5.nsv", "result2693_6.nsv", "result2693_7.nsv", "result2693_8.nsv", "result2693_9.nsv", "result2693_10.nsv", "result2693_11.nsv", "result2693_12.nsv", "result2693_13.nsv", "result2693_14.nsv", "result2693_15.nsv", "result2693_16.nsv", "result2693_17.nsv", "result2693_18.nsv", "result2693_19.nsv"];
val thyn = "vfmTestDefs2693";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
