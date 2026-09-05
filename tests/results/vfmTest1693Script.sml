Theory vfmTest1693[no_sig_docs]
Ancestors vfmTestDefs1693
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1693_0.nsv", "result1693_1.nsv", "result1693_2.nsv", "result1693_3.nsv", "result1693_4.nsv", "result1693_5.nsv", "result1693_6.nsv", "result1693_7.nsv", "result1693_8.nsv", "result1693_9.nsv", "result1693_10.nsv", "result1693_11.nsv", "result1693_12.nsv", "result1693_13.nsv", "result1693_14.nsv", "result1693_15.nsv", "result1693_16.nsv", "result1693_17.nsv", "result1693_18.nsv", "result1693_19.nsv"];
val thyn = "vfmTestDefs1693";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
