Theory vfmTest1282[no_sig_docs]
Ancestors vfmTestDefs1282
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1282_0.nsv", "result1282_1.nsv", "result1282_2.nsv", "result1282_3.nsv", "result1282_4.nsv", "result1282_5.nsv", "result1282_6.nsv", "result1282_7.nsv", "result1282_8.nsv"];
val thyn = "vfmTestDefs1282";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
