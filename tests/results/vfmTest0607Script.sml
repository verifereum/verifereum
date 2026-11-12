Theory vfmTest0607[no_sig_docs]
Ancestors vfmTestDefs0607
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0607_0.nsv", "result0607_1.nsv", "result0607_2.nsv", "result0607_3.nsv", "result0607_4.nsv", "result0607_5.nsv", "result0607_6.nsv", "result0607_7.nsv", "result0607_8.nsv", "result0607_9.nsv"];
val thyn = "vfmTestDefs0607";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
